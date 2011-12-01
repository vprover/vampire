/**
 * @file Log.cpp
 * Implements class Log.
 */

#include "Forwards.hpp"

#include "Lib/Backtrackable.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/Stack.hpp"
#include "Lib/System.hpp"

#include "Kernel/Unit.hpp"

#include "Log.hpp"

namespace Debug
{

using namespace Lib;

Logging::TagDeclTrigger s_trigger;

class Logging::Impl
{
  struct ChildInfo {
    unsigned childIndex;
    unsigned depth;

    ChildInfo() : childIndex(UINT_MAX) {}
    ChildInfo(unsigned childIndex, unsigned depth)
     : childIndex(childIndex), depth(depth) {}
  };
  struct TagInfo {
    typedef Stack<ChildInfo> ChildStack;

    string name;
    string doc;
    ChildStack children;

    bool enabled;
    /** Depth up to which children of this tag are enabled */
    unsigned enabledDepth;

    TagInfo(string name) : name(name), enabled(false) {}
  };

  struct TagEnableBO : public BacktrackObject {
    Logging::Impl& parent;
    unsigned _tagIdx;
    bool _oldEnabled;
    unsigned _oldDepth;

    TagEnableBO(Logging::Impl& parent, unsigned tagIdx, bool oldEnabled, unsigned oldDepth)
    : parent(parent), _tagIdx(tagIdx), _oldEnabled(oldEnabled), _oldDepth(oldDepth)
    {}

    virtual void backtrack() {
      ASS(parent._tags[_tagIdx].enabled);
      if(!_oldEnabled) {
	parent._tags[_tagIdx].enabled = false;
      }
      parent._tags[_tagIdx].enabledDepth = _oldDepth;
    }
  };

  DHMap<std::string, unsigned> _tagNums;
  Stack<TagInfo> _tags;

  Stack<BacktrackData> _stateStack;

  unsigned tag2idx(const char* tag) const {
    CALL("Logging::Impl::tag2idx");

    unsigned res;
    if(!_tagNums.find(tag, res)) {
      ASS_REP(false,tag);
      throw Exception("Tag \""+string(tag)+"\" does not exist.");
    }
    return res;
  }

  bool enableOneTag(unsigned tagIdx, unsigned enabledDepth) {
    TagInfo& ti = _tags[tagIdx];
    if(ti.enabled && enabledDepth<=ti.enabledDepth) {
      return false;
    }
    if(_stateStack.isNonEmpty()) {
      _stateStack.top().addBacktrackObject(new TagEnableBO(*this, tagIdx, ti.enabled, ti.enabledDepth));
    }
    ti.enabled = true;
    ti.enabledDepth = enabledDepth;
    return true;
  }
public:
  ~Impl() {
    while(_stateStack.isNonEmpty()) {
      _stateStack.pop().drop();
    }
  }

  /**
   * Declare new tag
   *
   * A tag of given name can be declared at most once
   */
  void declareTag(const char* tag)
  {
    CALL("Logging::Impl::declareTag");

    if(_tagNums.find(tag)) {
      ASSERTION_VIOLATION;
      throw Exception("Tag \""+string(tag)+"\" already declared.");
    }

    unsigned idx = _tags.size();
    _tags.push(TagInfo(tag));
    _tagNums.insert(tag,idx);
  }

  /**
   * Add documentation string to a tag
   */
  void addDoc(const char* tag, const char* doc)
  {
    CALL("Logging::Impl::declareTag");

    unsigned idx = tag2idx(tag);
    _tags[idx].doc = doc;
  }

  void addParent(const char* child, const char* parent, unsigned depth)
  {
    CALL("Logging::Impl::addParent");

    unsigned childIdx = tag2idx(child);
    unsigned parIdx = tag2idx(parent);

    _tags[parIdx].children.push(ChildInfo(childIdx, depth));
  }


  void pushTagStates()
  {
    CALL("Logging::Impl::pushTagStates");

    _stateStack.push(BacktrackData());
  }

  void popTagStates()
  {
    CALL("Logging::Impl::popTagStates");

    _stateStack.top().backtrack();
    _stateStack.pop();
  }

  /**
   * Enable tag @c tag and all its child tags up to the @c depthLimit.
   */
  void enableTag(const char* tag, unsigned depthLimit=UINT_MAX)
  {
    CALL("Logging::Impl::enableTag");

    static Stack<ChildInfo> todo;
    ASS(todo.isEmpty());

    todo.push(ChildInfo(tag2idx(tag), depthLimit));
    while(todo.isNonEmpty()) {
      ChildInfo cur = todo.pop();
      if(!enableOneTag(cur.childIndex, cur.depth)) {
	continue;
      }
      TagInfo& ti = _tags[cur.childIndex];
      TagInfo::ChildStack::Iterator cit(ti.children);
      while(cit.hasNext()) {
	ChildInfo ci = cit.next();
	if(ci.depth<=cur.depth) {
	  unsigned childDepthLimit = (depthLimit==UINT_MAX) ? UINT_MAX : (cur.depth-ci.depth);
	  todo.push(ChildInfo(ci.childIndex, childDepthLimit));
	}
      }
    }
  }

  void processTraceSpecString(std::string str)
  {
    CALL("Logging::Impl::processTraceSpecString");

    if(str.empty()) { return; }
    if(str=="help") {
      displayHelp();
      exit(0);
    }
    if(str=="help+") {
      //with this command we only display help but don't exit
      displayHelp();
    }

    DArray<char> chars;
    chars.initFromArray(str.size()+1, str.c_str());
    char* tagStart = chars.array();
    while(true) {
      char* tagEnd = tagStart;
      while(*tagEnd && *tagEnd!=':' && *tagEnd!=',') {
	++tagEnd;
      }
      if(tagStart==tagEnd) {
	USER_ERROR("Tag control string \""+string(str)+"\" is not valid.");
      }

      char* nextTagStart; //if zero, there is no next tag
      unsigned depth;
      if(*tagEnd==':') {
	char* depthStart = tagEnd+1;
	char* depthEnd = depthStart;
	while(*depthEnd && *depthEnd!=',') {
	  ++depthEnd;
	}
	if(*depthEnd) {
	  nextTagStart = depthEnd+1;
	}
	else {
	  nextTagStart = 0;
	}
	*depthEnd = 0;
	if(!Int::stringToUnsignedInt(depthStart, depth)) {
	  USER_ERROR("Tag control string \""+string(str)+"\" is not valid.");
	}
      }
      else {
	depth = UINT_MAX;
	if(*tagEnd) {
	  ASS_EQ(*tagEnd,',');
	  nextTagStart = tagEnd+1;
	}
	else {
	  nextTagStart = 0;
	}
      }
      *tagEnd=0;
      enableTag(tagStart, depth);

      if(nextTagStart==0) {
	break;
      }
      tagStart = nextTagStart;
    }
  }

  bool isTagEnabled(const char* tag)
  {
    CALL("Logging::Impl::isTagEnabled");

#if !VDEBUG
    if(!_tagNums.find(tag)) { return false; }
#endif

    unsigned idx = tag2idx(tag);
    return _tags[idx].enabled;
  }

  void displayHelp()
  {
    CALL("Logging::Impl::displayTagListAndExit");

    ostream& out = cerr;

    out << "Vampire trace output" << endl
	<< "Usage:" << endl
	<< "  " << System::guessExecutableName() << " -tr <trace string>" << endl
	<< "Trace string:" << endl
	<< "help" << endl
	<< "  ... show this help" << endl
	<< "[trace_name1[:depth_limit1][,trace_name2[:depth_limit2][,...]]]" << endl
	<< "  ... enable specified traces with child traces up to given depth or without limit" << endl
	<< endl
	<< "Traces:" << endl
	<< "(with each trace we specify its child traces together with their distance "
	   "from the parent that can be used for the depth limit)" << endl;


    unsigned tagCnt = _tags.size();
    for(unsigned i=0; i<tagCnt; ++i) {
      TagInfo& cur = _tags[i];
      out << cur.name << endl;
      if(!cur.doc.empty()) {
	out << "  " << cur.doc << endl;
      }
      if(cur.children.isNonEmpty()) {
	out << "  children: ";
	TagInfo::ChildStack::Iterator cit(cur.children);
	while(cit.hasNext()) {
	  ChildInfo ci = cit.next();
	  out << _tags[ci.childIndex].name << "(" << ci.depth << ")";
	  if(cit.hasNext()) {
	    out << ", ";
	  }
	}
	out << endl;
      }
    }
  }
};

Logging::Impl& Logging::impl()
{
  CALL("Logging::impl");

  static Impl impl;
  return impl;
}

void Logging::declareTag(const char* tag) {
  impl().declareTag(tag);
}
void Logging::addDoc(const char* tag, const char* doc) {
  impl().addDoc(tag,doc);
}
void Logging::addParent(const char* child, const char* parent, unsigned depth) {
  impl().addParent(child,parent,depth);
}
void Logging::enableTag(const char* tag, unsigned depthLimit) {
  impl().enableTag(tag,depthLimit);
}
void Logging::processTraceSpecString(std::string str) {
  impl().processTraceSpecString(str);
}

void Logging::pushTagStates() {
  impl().pushTagStates();
}
void Logging::popTagStates() {
  impl().popTagStates();
}

bool Logging::isTagEnabled(const char* tag) {
  return impl().isTagEnabled(tag);
}


void Logging::logUnit(const char* tag, Kernel::Unit* u)
{
  CALL("Logging::Impl::logUnit");
  tout << tag << ": " << u->toString() << std::endl;
}

void Logging::logSimpl(const char* tag, Kernel::Unit* src, Kernel::Unit* tgt, const char* doc)
{
  CALL("Logging::logSimpl");

  tout << tag << " simplification:" << endl
       << "   <- " << src->toString() << endl
       << "   -> " << tgt->toString() << endl;
  if(doc) {
    tout << "      (" << doc << ")" << endl;
  }
}

void Logging::logSimpl2(const char* tag, Kernel::Unit* prem1, Kernel::Unit* prem2, Kernel::Unit* tgt, const char* doc)
{
  CALL("Logging::logSimpl2");

  tout << tag << " simplification:" << endl
       << "   <- " << prem1->toString() << endl
       << "   <- " << prem2->toString() << endl
       << "   -> " << tgt->toString() << endl;
  if(doc) {
    tout << "      (" << doc << ")" << endl;
  }
}

void Logging::logTaut(const char* tag, Kernel::Unit* u, const char* doc)
{
  CALL("Logging::logSimpl");

  tout << tag << " discovered tautology:" << endl
       << "    " << u->toString() << endl;
  if(doc) {
    tout << "    (" << doc << ")" << endl;
  }
}


using namespace Lib;

/**
 * Return current process id for the purpose of log outputs
 */
size_t LOG_getpid()
{
  return System::getPID();
}

}
