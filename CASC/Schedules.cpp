/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Schedules.cpp
 * Implements class Schedules.
 * @since 09/15/2017
 * @author Martin Suda
 */

/* this translation unit causes the optimiser to take a very long time,
 * but it's not really performance-critical code:
 * disable optimisation for this file with various compilers */
#if defined(__clang__)
#pragma clang optimize off
#elif defined(__GNUC__)
#pragma GCC optimize 0
#endif

#include "Schedules.hpp"

#include "Shell/Options.hpp"

#include <fstream>

using namespace std;
using namespace Lib;
using namespace Shell;
using namespace CASC;

void Schedules::getScheduleFromFile(const std::string& filename, Schedule& quick)
{
  if (filename == "") {
    USER_ERROR("Schedule file was not set.");
  }
  ifstream schedule_file (filename.c_str());
  if (schedule_file.fail()) {
    USER_ERROR("Cannot open schedule file: " + filename);
  }
  ASS(schedule_file.is_open());
  std::string line;
  while (getline(schedule_file, line)) {
    // Allow structuring the schedule file with empty lines.
    // Allow documenting the schedule file with line comments.
    // Interpret lines that start with '%' as comments, following the TPTP convention.
    if (line == "" or line[0] == '%') {
      continue;
    }
    Options opts;
    try {
      opts.readFromEncodedOptions(line);
      opts.checkGlobalOptionConstraints();
    }
    catch (...) {
      USER_ERROR("Bad strategy: " + line);
    }
    quick.push(line);
  }
}

/**
 * Get schedules for a problem of given property.
 * The schedules are to be executed from the bottom of the stack, i.e. in the order in which they are mentioned in the file.
 */
void Schedules::getCasc2019Schedule(const Property& property, Schedule& quick, Schedule& fallback)
{
  Property::Category cat = property.category();
  unsigned long prop = property.props();
  unsigned atoms = property.atoms();

  // for theory problems, we make the schedule before the main choice
  if (prop & (524288ul | 1048576ul | 2097152ul)) { // contains integers, rationals and reals
    if ((prop & 67108864ul) == 0ul) { // no linear integer functions
      quick.push("dis+11_4_afp=100000:afq=1.1:anc=none:cond=on:gs=on:gsaa=full_model:nm=64:nwc=1:sac=on:sp=reverse_arity:thi=all_2");
      quick.push("ott+1010_2:1_awrs=decay:awrsf=512:acc=on:add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:ccuc=first:fsr=off:fde=unused:gsp=on:gs=on:gsaa=from_current:irw=on:nm=32:newcnf=on:nwc=1:sos=theory:sp=occurrence:tha=some:uwa=interpreted_only:updr=off_8");
      quick.push("lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2");
      quick.push("dis+10_5_add=off:afp=4000:afq=1.1:anc=none:cond=fast:ep=RSTC:fsr=off:gs=on:gsem=on:lwlo=on:nm=64:nwc=1:sp=reverse_arity:thi=all_3");
      quick.push("dis+10_1_add=off:afp=40000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:irw=on:nm=64:nwc=1:sas=z3:sac=on_2");
      quick.push("dis+11_3_add=off:afp=10000:afq=2.0:amm=sco:anc=none:ep=RST:gs=on:gsaa=from_current:gsem=on:inw=on:nm=64:nwc=1:sd=10:ss=axioms:st=5.0:sos=all:tha=off:updr=off:uhcvi=on_59");
      quick.push("lrs+10_2_add=off:afr=on:afp=4000:afq=2.0:amm=off:anc=none:cond=fast:fsr=off:fde=unused:gs=on:gsaa=full_model:gsem=on:inw=on:nm=64:nwc=1:sas=z3:stl=30:sos=all:sp=occurrence:tha=off:thf=on:urr=on:updr=off:uhcvi=on_2");
      quick.push("lrs+1_1024_av=off:bs=on:fde=none:inw=on:irw=on:nm=64:nwc=1.2:stl=60:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_595");
      quick.push("dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_229");
      quick.push("dis+10_10_add=large:afp=4000:afq=1.1:amm=sco:anc=none:irw=on:lcm=reverse:lma=on:nm=6:nwc=1:sos=all:sac=on:sp=reverse_arity:urr=on_30");
      quick.push("ott-2_64_add=large:afr=on:afp=4000:afq=1.1:amm=sco:anc=none:bd=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:newcnf=on:nwc=1:sac=on:sp=occurrence:thf=on:updr=off:uhcvi=on_154");
      quick.push("dis+11_3_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bd=preordered:bce=on:fsr=off:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1:sd=10:ss=axioms:st=5.0:sac=on:sp=occurrence:tha=off:urr=ec_only_85");
      quick.push("ott-11_3_add=large:afp=100000:afq=1.2:anc=none:bs=on:cond=fast:fde=none:gs=on:gsem=off:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sos=all:sp=occurrence:tha=off:urr=on:uhcvi=on_268");
    }
    else if (prop == 604504064ul) {
      quick.push("dis+11_4_afp=100000:afq=1.1:anc=none:cond=on:gs=on:gsaa=full_model:nm=64:nwc=1:sac=on:sp=reverse_arity:thi=all_2");
      quick.push("dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=on:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670");
    }
    else {
      quick.push("ott+10_3:2_aac=none:add=large:afp=10000:afq=2.0:amm=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=off:lcm=reverse:lma=on:nm=0:nwc=4:sas=z3:updr=off_22");
      quick.push("ott+1_3:1_av=off:bd=off:fsr=off:fde=none:gs=on:inw=on:nm=2:nwc=1.5:sp=frequency:uwa=one_side_interpreted_22");
      quick.push("dis+1011_5_aac=none:add=large:afp=40000:afq=1.2:amm=off:anc=none:bd=off:fsr=off:gsp=on:inw=on:irw=on:lma=on:nm=64:nwc=1:sas=z3:sos=on:sp=occurrence:tha=off:updr=off_26");
      quick.push("lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_29");
      quick.push("lrs-11_1_av=off:cond=on:gs=on:lcm=reverse:lma=on:lwlo=on:nm=16:nwc=5:stl=30:sp=reverse_arity:tha=off:thi=strong:uwa=interpreted_only_58");
      quick.push("dis-3_4_add=off:afp=40000:afq=1.1:amm=off:anc=none:bs=unit_only:cond=fast:fsr=off:gs=on:inw=on:lma=on:nm=64:nwc=1.5:nicw=on:sas=z3:sp=reverse_arity:tha=off:thf=on:uhcvi=on_13");
      quick.push("lrs+1_5:4_aac=none:add=off:afr=on:afp=4000:afq=1.2:amm=sco:anc=none:gsp=on:gs=on:irw=on:nm=64:newcnf=on:nwc=1.3:nicw=on:sas=z3:stl=30:sp=occurrence:tha=off_3");
      quick.push("dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7");
      quick.push("dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12");
      quick.push("lrs+3_128_awrs=converge:awrsf=2:av=off:bs=on:cond=fast:fsr=off:fde=unused:gsp=on:irw=on:lma=on:nm=64:nwc=1.5:stl=30:sp=frequency:tha=some:updr=off_148");
      quick.push("dis+11_6_add=large:afr=on:afp=100000:afq=1.2:amm=off:anc=none:cond=fast:gs=on:gsaa=from_current:gsem=off:irw=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sos=on:sp=occurrence:tha=off:thi=strong:updr=off_2");
      quick.push("dis+10_3:2_afr=on:afp=1000:afq=1.2:bd=off:irw=on:lcm=predicate:lwlo=on:nm=0:newcnf=on:nwc=2:sos=on:tha=off:thf=on:urr=ec_only_11");
      quick.push("dis+1010_2:3_add=off:afr=on:afp=10000:afq=1.1:anc=none:fsr=off:gs=on:gsem=off:nwc=1:sas=z3:sos=all:sac=on:sp=reverse_arity:tha=off_5");
      quick.push("dis-10_4:1_aac=none:add=off:afp=1000:afq=1.4:amm=off:anc=none:cond=fast:ep=RSTC:gs=on:gsaa=from_current:gsem=on:inw=on:lma=on:nm=64:nwc=4:sas=z3:tha=off:thi=strong:uwa=interpreted_only:updr=off:uhcvi=on_6");
      quick.push("lrs+1_2:3_afr=on:afp=1000:afq=1.1:amm=sco:anc=none:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:lma=on:nm=64:nwc=1.3:sas=z3:stl=30:sac=on:tha=off:uwa=one_side_interpreted:updr=off_9");
      quick.push("lrs+10_2_add=off:afr=on:afp=4000:afq=2.0:amm=off:anc=none:cond=fast:fsr=off:fde=unused:gs=on:gsaa=full_model:gsem=on:inw=on:nm=64:nwc=1:sas=z3:stl=30:sos=all:sp=occurrence:tha=off:thf=on:urr=on:updr=off:uhcvi=on_6");
      quick.push("lrs+1011_1_add=off:afp=100000:afq=1.0:anc=none:cond=on:gs=on:gsaa=from_current:gsem=on:inw=on:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sos=on:sp=occurrence:tha=off:uwa=ground_3");
      quick.push("dis+1010_4_add=off:afp=100000:afq=1.0:anc=none:fsr=off:gs=on:gsem=off:inw=on:irw=on:lma=on:nm=64:nwc=1:sas=z3:sos=on:sac=on:tha=off:thf=on_179");
      quick.push("lrs-2_24_awrs=converge:awrsf=64:av=off:bd=off:bs=on:bsr=on:br=off:cond=on:fde=none:gsp=on:inw=on:lwlo=on:nm=6:nwc=4:stl=30:s2a=on:sos=all:sp=weighted_frequency:thf=on:uwa=one_side_interpreted:urr=on:updr=off:uhcvi=on:uwaf=on_21");
      quick.push("ott+10_8_add=large:afp=100000:afq=1.4:amm=sco:cond=fast:fsr=off:fde=none:lcm=predicate:lma=on:nm=32:nwc=1:sos=on:sac=on:tha=off:updr=off_29");
      quick.push("dis-2_2:3_add=large:afp=40000:afq=1.4:amm=off:anc=none:gsp=on:gs=on:gsem=on:inw=on:lcm=reverse:lma=on:nm=2:nwc=1:nicw=on:sas=z3:sos=all:sp=reverse_arity:tha=off:urr=on_5");
      quick.push("dis+1_3:1_acc=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:cond=on:fsr=off:gs=on:inw=on:lma=on:nm=32:nwc=1:urr=on_2");
      quick.push("dis+1011_2:3_add=off:afr=on:afp=4000:afq=1.4:anc=none:bs=unit_only:fsr=off:gs=on:gsem=on:lwlo=on:nm=16:nwc=1.3:nicw=on:sas=z3:sac=on:tha=off_260");
      quick.push("dis+1010_24_aac=none:afr=on:anc=none:cond=on:fsr=off:gs=on:gsem=on:nm=6:nwc=1:sas=z3:sos=on:sp=reverse_arity:tha=off_9");
      quick.push("dis+11_3_add=large:afr=on:afp=4000:afq=1.2:amm=off:anc=none:gs=on:gsem=on:lwlo=on:nm=64:nwc=1:sas=z3:sac=on:sp=reverse_arity:tha=off:thf=on:updr=off_92");
      quick.push("lrs+1003_2_awrs=converge:awrsf=512:add=large:afp=10000:afq=1.1:amm=sco:anc=none:cond=fast:fde=unused:lma=on:nm=64:nwc=1.2:stl=30:s2a=on:sac=on:sp=reverse_arity:tha=some:thi=new:urr=on:updr=off_80");
      quick.push("ott+10_4_awrs=converge:awrsf=128:afp=100000:afq=1.4:amm=sco:anc=none:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:s2a=on:sac=on:sp=frequency:tha=off_3");
      quick.push("dis+10_6_afr=on:afp=1000:afq=1.2:anc=none:bsr=on:fsr=off:gs=on:lcm=reverse:nm=64:newcnf=on:nwc=1.7:sas=z3:tha=off_4");
      quick.push("lrs+10_8:1_aac=none:add=off:afr=on:afp=40000:afq=1.1:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=none:gs=on:gsem=off:nm=0:nwc=1.2:sas=z3:stl=30:sos=all:sp=reverse_arity:tha=off:updr=off_68");
      quick.push("dis+1002_4_add=off:afp=10000:afq=2.0:amm=off:anc=none:fsr=off:gsp=on:gs=on:gsem=on:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1:sos=on:sac=on:sp=occurrence:tha=off:updr=off_2");
      quick.push("lrs-11_3:1_awrs=converge:awrsf=1:av=off:bce=on:cond=fast:fde=none:gs=on:gsem=off:lwlo=on:nm=16:newcnf=on:nwc=2:stl=90:s2a=on:sos=theory:sp=weighted_frequency:tha=some:uwa=one_side_constant:urr=on:updr=off:uhcvi=on_234");
      quick.push("dis-1_2:1_afr=on:afp=10000:afq=2.0:anc=none:cond=on:fsr=off:fde=unused:gs=on:gsaa=full_model:gsem=on:inw=on:irw=on:lcm=predicate:lma=on:nm=32:nwc=1:sas=z3:sos=all:sp=reverse_arity:tha=off:uwa=ground_4");
      quick.push("lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_359");
      quick.push("dis+11_3_afp=100000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:inw=on:lma=on:nm=64:nwc=1:sas=z3:sd=10:ss=axioms:st=5.0:sp=occurrence:tha=off:updr=off_202");
      quick.push("lrs-11_4_awrs=decay:awrsf=64:afp=1000:afq=2.0:amm=off:anc=none:br=off:cond=on:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:s2a=on:sos=theory:sac=on:sp=frequency:tha=some:thi=new:urr=on:uhcvi=on_6");
      quick.push("ott+1004_5_av=off:bd=off:bs=on:cond=on:fde=none:lma=on:nm=64:nwc=1:sos=on:sp=reverse_arity:tha=off:thi=strong:uwa=one_side_constant_143");
      quick.push("lrs+1011_7_aac=none:add=large:afr=on:afp=40000:afq=1.4:bd=off:bs=on:bsr=on:fsr=off:inw=on:lma=on:nm=64:nwc=2:nicw=on:sas=z3:stl=60:sos=all:sp=reverse_arity:tha=off:updr=off:uhcvi=on_541");
    }
    // add very long final fallback strategy from UFLIA problems
    fallback.push("lrs+1011_2:1_afr=on:afp=10000:afq=2.0:amm=off:gsp=on:gs=on:inw=on:ile=on:nm=2:nwc=1:sas=z3:tha=off_300");
    fallback.push("ott+1010_2:1_acc=on:add=large:afr=on:afp=40000:afq=1.1:anc=none:gs=on:inw=on:ile=on:nm=64:newcnf=on:nwc=1:sos=on:sac=on:sp=reverse_arity:urr=on_300");
    fallback.push("dis+2_1_add=large:afr=on:afp=1000:afq=1.2:anc=none:cond=on:nm=64:newcnf=on:nwc=1:tha=off:updr=off_300");
    fallback.push("ott+10_4:1_aac=none:add=off:afp=40000:afq=1.1:amm=sco:anc=none:bd=off:gs=on:gsem=off:ile=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:sp=reverse_arity:tha=off:updr=off_300");
    fallback.push("dis+1011_2_acc=on:afp=10000:afq=1.1:amm=sco:anc=none:ccuc=small_ones:cond=fast:fde=unused:lma=on:nm=64:newcnf=on:nwc=1:sac=on:sp=reverse_arity:tha=off:updr=off:uhcvi=on_300");
    fallback.push("ott+11_5:4_aac=none:add=large:afp=4000:afq=1.4:amm=sco:anc=none:cond=fast:fde=none:gs=on:gsem=on:inw=on:ile=on:nm=2:newcnf=on:nwc=1:sas=z3:sos=on:sp=reverse_arity:urr=on:uhcvi=on_300");
    fallback.push("dis+10_14_add=large:afp=4000:afq=1.1:amm=sco:bs=unit_only:bsr=on:cond=fast:fde=none:inw=on:irw=on:lcm=predicate:nm=4:nwc=1.1:sos=on:sac=on:updr=off:uhcvi=on_300");
    fallback.push("dis+1002_5:4_add=off:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fsr=off:inw=on:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:tha=off:updr=off_300");
    fallback.push("lrs+11_5:1_add=off:afp=100000:afq=1.1:amm=off:anc=none:bd=off:cond=on:er=known:gs=on:gsem=off:inw=on:ile=on:irw=on:lcm=predicate:lwlo=on:nm=64:newcnf=on:nwc=1.1:sac=on:sp=reverse_arity:tha=off:thf=on_300");
    fallback.push("dis+1011_5:1_afp=4000:afq=1.4:amm=off:anc=none:cond=on:fde=unused:gsp=on:ile=on:lma=on:nm=16:nwc=1:sos=on:sac=on:tha=off:urr=ec_only:uhcvi=on_300");
    fallback.push("dis+1010_1_add=off:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:gs=on:gsem=off:inw=on:ile=on:irw=on:nm=6:nwc=1.3:nicw=on:sas=z3:tha=off:urr=ec_only_300");
    fallback.push("dis+1002_2_aac=none:add=off:afr=on:afp=100000:afq=1.2:amm=sco:anc=all:bsr=on:fde=unused:inw=on:ile=on:lcm=reverse:nm=4:nwc=4:nicw=on:sos=theory:sac=on:sp=reverse_arity:uhcvi=on_300");
    fallback.push("lrs+1011_8:1_add=off:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:fsr=off:gs=on:gsem=off:ile=on:irw=on:nm=2:nwc=1:sas=z3:sp=reverse_arity:tha=off:urr=on:updr=off_300");
    fallback.push("ott+1002_3:1_av=off:bsr=on:ep=RS:inw=on:ile=on:lma=on:nm=64:newcnf=on:nwc=1:sp=occurrence:tha=off:updr=off:uhcvi=on_300");
    fallback.push("lrs+1011_3_add=off:afp=1000:afq=2.0:amm=off:anc=none:bsr=on:bce=on:cond=fast:fde=unused:ile=on:lma=on:nm=6:nwc=2:nicw=on:sas=z3:sd=3:ss=axioms:st=2.0:sp=reverse_arity:tha=off_300");
    fallback.push("ott+1011_3:2_av=off:bd=off:bs=on:bce=on:cond=on:fde=unused:ile=on:lma=on:newcnf=on:nwc=1:tha=off:updr=off_300");
    fallback.push("dis+11_3:1_av=off:br=off:ep=R:fsr=off:gsp=on:ile=on:lma=on:nm=2:newcnf=on:nwc=1:sas=z3:sp=reverse_arity:urr=on:uhcvi=on_300");
    fallback.push("lrs-2_8:1_add=large:afp=100000:afq=1.4:amm=sco:anc=none:bs=on:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=4:nicw=on:sas=z3:sp=reverse_arity:updr=off_600");
    fallback.push("dis+1010_2_acc=on:afr=on:afp=100000:afq=1.2:anc=none:bsr=on:fsr=off:ile=on:irw=on:nm=16:newcnf=on:nwc=4:sp=occurrence:tha=off:urr=ec_only_300");
    fallback.push("ott+1010_1_add=large:afp=1000:afq=1.2:anc=none:bd=off:ile=on:nm=2:newcnf=on:nwc=1:sp=occurrence:updr=off_300");
    fallback.push("lrs+1002_2_add=large:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:inw=on:lwlo=on:nm=32:newcnf=on:nwc=1:sos=theory:sac=on:sp=occurrence:urr=on_300");
    fallback.push("lrs-10_3_av=off:bs=unit_only:bsr=on:cond=on:fsr=off:fde=unused:gs=on:inw=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.2:sas=z3:tha=off:urr=ec_only_300");
    fallback.push("dis+10_3_add=off:afp=100000:afq=1.4:amm=sco:anc=none:fsr=off:gs=on:gsem=on:inw=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sp=reverse_arity:tha=off:thf=on:updr=off_300");
    fallback.push("lrs+2_4_add=large:afr=on:afp=100000:afq=1.1:amm=sco:anc=none:cond=on:ep=R:gs=on:gsaa=from_current:gsem=off:ile=on:lcm=reverse:lma=on:nm=2:nwc=1.1:sos=on:sac=on:tha=off:updr=off_300");
    fallback.push("lrs+2_1024_av=off:bd=off:bsr=on:cond=fast:fsr=off:fde=none:ile=on:irw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:tha=off:thi=overlap:uwa=one_side_constant:updr=off:uhcvi=on_300");
    fallback.push("ott+1011_8:1_afr=on:afp=1000:afq=1.4:amm=sco:anc=none:bd=off:fsr=off:fde=unused:inw=on:ile=on:nm=2:nwc=1:nicw=on:sas=z3:sos=theory:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_600");
    fallback.push("lrs+10_2:3_afr=on:afp=1000:afq=1.1:bd=off:bce=on:cond=on:gsp=on:gs=on:gsaa=from_current:inw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:sp=reverse_arity:tha=off:uwa=interpreted_only:updr=off:uhcvi=on_300");
    fallback.push("dis+10_32_add=large:afp=40000:afq=1.0:anc=none:bd=off:bsr=on:fde=none:lma=on:nm=0:newcnf=on:nwc=1:nicw=on:sp=occurrence:tha=off:thi=full:uhcvi=on_300");
    fallback.push("ott+1010_2:1_add=off:afr=on:afp=1000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:ile=on:nm=64:newcnf=on:nwc=1:sd=2:ss=axioms:st=1.5:sac=on:tha=off:updr=off_300");
    fallback.push("lrs-11_2:1_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:inw=on:ile=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.5:sas=z3:sp=reverse_arity:urr=on_300");
    fallback.push("dis+11_7_add=large:afr=on:afp=10000:afq=1.2:bd=off:bsr=on:cond=on:fsr=off:fde=unused:gs=on:ile=on:lcm=predicate:lma=on:nm=2:newcnf=on:nwc=3:sos=on:sp=reverse_arity:tha=off:updr=off_300");
    fallback.push("dis+1011_1_afp=40000:afq=1.2:anc=none:cond=on:gsp=on:ile=on:irw=on:lma=on:newcnf=on:nwc=1:sac=on:sp=occurrence:tha=off:updr=off_300");
    fallback.push("lrs+10_3_av=off:fde=unused:gs=on:gsem=on:inw=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1.7:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_600");
    fallback.push("lrs+11_2:1_add=off:anc=none:bsr=on:br=off:cond=on:er=filter:fsr=off:gs=on:gsem=on:inw=on:ile=on:lma=on:nm=2:nwc=1:sas=z3:sos=all:sac=on:uwa=ground:urr=on_300");
    fallback.push("lrs+1003_3:2_afp=1000:afq=2.0:amm=off:anc=none:cond=on:gs=on:ile=on:lma=on:nm=6:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off:thi=all:updr=off_300");
    fallback.push("lrs+4_8:1_av=off:cond=on:gs=on:gsem=on:irw=on:nm=64:newcnf=on:nwc=1.1:sp=occurrence:tha=off:urr=on:updr=off_300");
    fallback.push("ott-4_5:4_aac=none:afr=on:afp=100000:afq=1.2:amm=sco:anc=none:bd=off:bsr=on:br=off:cond=fast:ile=on:irw=on:lcm=reverse:lma=on:nm=64:newcnf=on:nwc=3:thf=on:urr=on:updr=off:uhcvi=on_300");
    fallback.push("dis+1011_3_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fde=none:gs=on:gsem=off:ile=on:lma=on:lwlo=on:nm=4:nwc=1:sac=on:tha=off:updr=off:uhcvi=on_300");
    fallback.push("lrs+1011_2:1_av=off:fsr=off:gs=on:gsem=off:inw=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1:sp=occurrence:tha=off:urr=ec_only:uhcvi=on_300");
    fallback.push("dis+1011_4_afr=on:afp=10000:afq=1.1:amm=off:anc=none:ep=RS:fsr=off:ile=on:nm=64:newcnf=on:nwc=1:sos=all:sac=on:updr=off:uhcvi=on_300");
    fallback.push("lrs+1010_1_afp=1000:afq=1.4:amm=off:anc=none:bd=off:bsr=on:br=off:cond=on:ile=on:irw=on:nm=2:nwc=1:nicw=on:sas=z3:sos=all:sp=reverse_arity:tha=off:urr=on:updr=off_300");
    fallback.push("lrs+10_24_afp=4000:afq=2.0:bd=off:bsr=on:bce=on:cond=fast:fsr=off:gsp=on:gs=on:gsem=on:inw=on:ile=on:nwc=1.3:sp=occurrence:tha=off:uwa=one_side_constant:urr=ec_only_300");
    fallback.push("lrs-2_5:1_acc=on:add=off:afr=on:afp=40000:afq=1.1:amm=off:anc=none:bd=off:cond=fast:gs=on:ile=on:nm=0:newcnf=on:nwc=3:sac=on:thf=on:urr=ec_only_300");
    fallback.push("lrs+1_5:1_add=off:afr=on:afp=40000:afq=2.0:amm=off:anc=none:cond=on:gs=on:gsem=off:ile=on:lma=on:nm=64:nwc=1.2:sp=reverse_arity_300");
    fallback.push("lrs+1010_1_add=large:afr=on:afp=40000:afq=2.0:anc=none:br=off:fsr=off:inw=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sos=all:urr=on_300");
    fallback.push("lrs+1011_2:1_aac=none:add=off:afp=1000:afq=1.0:amm=off:bs=on:gs=on:gsaa=from_current:gsem=on:ile=on:lcm=reverse:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sp=reverse_arity:tha=off_300");
    fallback.push("dis+1010_2_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:bd=off:fsr=off:fde=none:ile=on:lcm=reverse:lma=on:nm=64:nwc=1:nicw=on:sas=z3:sp=reverse_arity_300");
    fallback.push("ott+1011_3:1_add=off:afp=100000:afq=2.0:amm=off:anc=none:bs=unit_only:gs=on:gsem=on:irw=on:newcnf=on:nwc=1:sas=z3:tha=off_300");
    fallback.push("dis-3_7_av=off:bs=unit_only:bsr=on:cond=on:fsr=off:fde=none:gsp=on:ile=on:irw=on:lma=on:nm=4:nwc=1:sos=all:sp=occurrence:tha=off:thi=overlap:uwa=interpreted_only:uhcvi=on_300");
    fallback.push("dis+11_32_add=large:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:er=filter:ile=on:lcm=predicate:lma=on:newcnf=on:nwc=5:sp=occurrence:updr=off_300");
    fallback.push("lrs+1011_2:1_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:bd=preordered:ccuc=first:cond=fast:fsr=off:fde=unused:inw=on:ile=on:irw=on:lma=on:nm=64:nwc=2:nicw=on:sp=occurrence:urr=ec_only:updr=off_300");
    fallback.push("lrs+2_8_av=off:bsr=on:cond=on:fsr=off:ile=on:lma=on:nm=64:nwc=1.2:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_300");
    fallback.push("lrs+1002_1_add=off:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:fsr=off:gsp=on:inw=on:ile=on:lcm=predicate:lwlo=on:nm=64:nwc=1.7:sas=z3:sac=on:sp=reverse_arity:tha=off:thf=on_300");
    fallback.push("ott+10_4:1_afp=100000:afq=1.1:anc=none:bd=off:inw=on:ile=on:irw=on:lma=on:nm=4:nwc=1:sos=all:sac=on:sp=occurrence:tha=off:urr=on:updr=off_300");
    fallback.push("dis+1011_5:1_afr=on:afp=10000:afq=1.2:amm=sco:bd=preordered:bs=unit_only:cond=on:fsr=off:inw=on:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=1.1:sd=7:ss=axioms:st=1.2:tha=off:uhcvi=on_300");
    fallback.push("dis+1011_3_aac=none:afr=on:afp=40000:afq=1.4:amm=off:bs=on:fsr=off:fde=none:gsp=on:nm=64:newcnf=on:nwc=1:sac=on:sp=reverse_arity:tha=off_300");
    fallback.push("lrs+4_4_av=off:bd=off:bs=unit_only:cond=fast:fsr=off:fde=unused:gs=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1:sp=occurrence:tha=off:thf=on:updr=off_300");
    fallback.push("lrs+11_10_add=off:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:bce=on:cond=fast:gsp=on:inw=on:lma=on:nm=4:newcnf=on:nwc=1:sp=occurrence:tha=off:thf=on:urr=ec_only:uhcvi=on_300");
    fallback.push("ott+1011_2:3_av=off:bs=unit_only:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:nm=2:newcnf=on:nwc=1:sp=reverse_arity:tha=off:thi=all:uwa=all:urr=on:uhcvi=on_300");
    fallback.push("lrs+11_6_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:cond=fast:ile=on:nm=16:newcnf=on:nwc=1:sas=z3:sp=reverse_arity:tha=off:uhcvi=on_300");
    fallback.push("ott+1011_2:3_add=large:afr=on:afp=40000:afq=2.0:anc=none:br=off:bce=on:cond=fast:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:newcnf=on:nwc=1.1:sp=reverse_arity:tha=off:urr=on:updr=off_300");
    fallback.push("lrs+4_8:1_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:ile=on:irw=on:lcm=reverse:lma=on:nm=2:nwc=1:sos=all:tha=off_300");
    fallback.push("lrs-2_3:1_add=off:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:cond=on:er=filter:fde=unused:ile=on:irw=on:nm=64:newcnf=on:nwc=1.1:sas=z3:sac=on:sp=reverse_arity:tha=off:thf=on:thi=strong:uhcvi=on_600");
    fallback.push("dis+1011_10_av=off:bd=off:cond=fast:er=known:inw=on:ile=on:irw=on:lma=on:nwc=1.7:sp=occurrence:tha=off:uhcvi=on_300");
    fallback.push("dis+1010_3_afp=10000:afq=2.0:amm=off:anc=none:cond=on:fsr=off:gs=on:gsem=off:inw=on:ile=on:irw=on:nm=64:nwc=1:sas=z3:tha=off:urr=on_300");
    fallback.push("lrs+2_3:2_av=off:cond=fast:inw=on:ile=on:nm=2:nwc=1:sos=theory:urr=on_300");
    fallback.push("lrs+11_2_av=off:cond=on:fsr=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sp=reverse_arity:tha=off:thf=on_300");
    fallback.push("dis+10_2:1_aac=none:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:cond=on:fsr=off:gs=on:gsem=on:inw=on:ile=on:irw=on:nm=2:nwc=1.1:nicw=on:sas=z3:sos=theory:urr=on:updr=off_300");
    fallback.push("ott+1003_12_add=large:anc=all:bd=preordered:bce=on:fde=none:lcm=reverse:lma=on:nm=0:newcnf=on:nwc=1:nicw=on:sac=on:sp=reverse_arity:tha=off:uwa=ground_600");
    fallback.push("dis+1011_1_aac=none:add=large:afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bce=on:cond=on:er=known:fde=none:gsp=on:gs=on:gsaa=from_current:gsem=off:ile=on:newcnf=on:nwc=1:sas=z3:ss=axioms:st=2.0:sp=occurrence:tha=off:urr=ec_only_300");
    fallback.push("dis+1002_1_add=large:afp=4000:afq=1.2:anc=none:cond=on:fsr=off:gs=on:gsem=off:ile=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:sp=occurrence:tha=off:thi=strong:uwa=interpreted_only:uhcvi=on_300");
    fallback.push("dis+2_4_afp=10000:afq=1.1:bd=off:bs=on:cond=on:er=filter:ile=on:newcnf=on:nwc=1:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_300");
    fallback.push("lrs+1003_8:1_av=off:fsr=off:fde=unused:gsp=on:gs=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sos=on_300");
    fallback.push("lrs+11_8:1_afp=100000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:cond=on:fsr=off:gs=on:gsem=off:ile=on:irw=on:lcm=reverse:nm=64:nwc=2:nicw=on:sac=on:sp=occurrence:urr=on:updr=off_300");
    fallback.push("lrs-11_8:1_afr=on:afp=1000:afq=1.4:amm=off:anc=none:bd=off:bs=on:gs=on:ile=on:lcm=predicate:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off:thi=strong:uwa=interpreted_only_300");
    fallback.push("lrs+10_3:1_add=large:afp=10000:afq=1.1:amm=off:anc=none:cond=on:gs=on:gsem=off:inw=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1:sd=5:ss=axioms:st=1.5:tha=off:urr=on_300");
    fallback.push("lrs+1010_3:1_av=off:bd=off:bsr=on:irw=on:nm=64:newcnf=on:nwc=1.7:sos=all:updr=off_300");
    fallback.push("dis+11_5:1_afr=on:afp=40000:afq=2.0:amm=sco:anc=all_dependent:cond=fast:fde=unused:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=2:nwc=1:sos=all:urr=on:uhcvi=on_300");
    fallback.push("lrs+1004_1_aac=none:add=off:afr=on:afp=10000:afq=1.0:amm=sco:anc=all_dependent:bd=off:cond=fast:fsr=off:gs=on:gsaa=from_current:lcm=reverse:nm=0:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off:thf=on:urr=on:updr=off_300");
    fallback.push("lrs-10_3:2_aac=none:add=off:afr=on:afp=4000:afq=1.4:amm=off:anc=none:bd=off:bsr=on:fsr=off:ile=on:irw=on:lcm=reverse:lma=on:lwlo=on:nm=16:nwc=1:nicw=on:sas=z3:sd=2:ss=axioms:sos=on:sp=occurrence:updr=off_600");
    fallback.push("ott+1002_2:1_add=large:afr=on:afp=100000:afq=1.1:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=from_current:irw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off:updr=off_300");
    fallback.push("dis-4_7_acc=on:afp=40000:afq=1.4:anc=all_dependent:bsr=on:br=off:bce=on:ccuc=first:er=filter:fsr=off:fde=unused:gsp=on:ile=on:lcm=reverse:lma=on:nm=4:newcnf=on:nwc=1:nicw=on:sac=on:sp=reverse_arity:tha=off:thi=full:uwa=ground:urr=on:updr=off:uhcvi=on_300");
    fallback.push("ott-1_1_acc=model:add=off:afr=on:afp=4000:afq=1.2:anc=all:bd=preordered:bs=unit_only:bsr=on:ccuc=first:gs=on:gsaa=from_current:ile=on:nm=64:newcnf=on:nwc=1:nicw=on:sac=on:sp=occurrence:tha=off:thi=strong:updr=off_300");
    fallback.push("lrs+1011_5:4_av=off:bd=off:bs=on:cond=on:er=known:gs=on:gsem=on:inw=on:ile=on:lcm=reverse:nm=6:newcnf=on:nwc=1:sp=occurrence:tha=off:uhcvi=on_300");
    fallback.push("dis+1002_14_av=off:cond=fast:fde=unused:inw=on:ile=on:lma=on:nm=0:nwc=1:sos=all:sp=reverse_arity:tha=off:uwa=one_side_interpreted:uhcvi=on_300");
    fallback.push("dis+1011_8:1_add=off:afp=10000:afq=1.1:anc=none:bce=on:er=filter:gs=on:gsaa=from_current:gsem=off:inw=on:ile=on:lma=on:nm=2:nwc=3:sac=on:urr=on:updr=off_300");
    fallback.push("dis+4_4:1_add=off:afp=4000:afq=1.2:amm=sco:anc=none:br=off:cond=fast:ep=RS:fsr=off:inw=on:lma=on:nm=2:newcnf=on:nwc=1:sp=reverse_arity:tha=off:thf=on:urr=on:uhcvi=on_300");
    fallback.push("lrs+1002_1_aac=none:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ile=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1:sac=on:sp=occurrence:tha=off:updr=off_300");
    fallback.push("lrs+1002_2:1_aac=none:add=large:afr=on:afp=40000:afq=1.1:amm=off:anc=none:cond=fast:gs=on:nm=64:newcnf=on:nwc=1.5:sas=z3:sp=occurrence:updr=off_300");
    fallback.push("lrs+10_3:1_afp=1000:afq=1.4:amm=off:anc=none:bsr=on:inw=on:ile=on:lma=on:nm=0:newcnf=on:nwc=1:sas=z3:sac=on:tha=off:urr=on:updr=off_300");
    fallback.push("ott+10_2:1_av=off:bd=off:br=off:cond=fast:fsr=off:fde=none:gs=on:gsem=off:irw=on:nm=64:newcnf=on:nwc=1:sos=all:urr=on:updr=off:uhcvi=on_300");
    fallback.push("lrs+10_24_av=off:bs=unit_only:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sd=7:ss=axioms:st=1.2:sp=occurrence:tha=off:thf=on:uhcvi=on_600");
    fallback.push("lrs+4_28_afp=10000:afq=1.2:amm=sco:anc=none:bd=off:bce=on:cond=on:fsr=off:ile=on:irw=on:lcm=reverse:nm=16:newcnf=on:nwc=2:sas=z3:sp=occurrence:tha=off:updr=off:uhcvi=on_600");
    return;
  }

  switch (cat) {
  case Property::EPR:
    if (prop != 0UL) {
      quick.push("ott+10_64_add=off:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:lcm=predicate:lma=on:nwc=1:sac=on:sp=reverse_arity:urr=on_50");
      quick.push("lrs+1_16_add=off:afp=100000:afq=1.0:amm=off:cond=fast:er=filter:lcm=predicate:lma=on:lwlo=on:nwc=2:nicw=on:stl=60:sd=7:ss=axioms:st=5.0:sos=theory:sp=reverse_arity:urr=ec_only_344");
      quick.push("lrs+2_64_add=large:afp=40000:afq=1.1:bd=off:bs=on:bsr=on:bce=on:fde=unused:irw=on:lma=on:lwlo=on:nwc=1:stl=30:uhcvi=on_301");
      quick.push("dis+4_5_afp=1000:afq=1.1:amm=off:anc=none:bd=off:gs=on:irw=on:lcm=predicate:lma=on:nwc=1:sas=z3:sos=all:sp=occurrence_151");
      quick.push("dis+11_2:3_add=large:afp=10000:afq=1.2:anc=none:bd=off:bce=on:cond=fast:er=filter:fsr=off:fde=unused:gsp=on:nwc=5:sos=theory:sac=on:urr=on_245");
    }
    else if (atoms < 2000) {
      quick.push("ott+10_64_add=off:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:lcm=predicate:lma=on:nwc=1:sac=on:sp=reverse_arity:urr=on_47");
      quick.push("lrs+2_64_add=large:afp=40000:afq=1.1:bd=off:bs=on:bsr=on:bce=on:fde=unused:irw=on:lma=on:lwlo=on:nwc=1:stl=30:uhcvi=on_25");
      quick.push("lrs+1011_14_afr=on:afp=100000:afq=1.1:anc=none:bd=off:bsr=on:irw=on:nwc=1:sas=z3:stl=30_90");
      quick.push("lrs+1003_10_afp=4000:afq=1.2:amm=sco:anc=none:bd=off:bsr=on:br=off:bce=on:fde=unused:lma=on:nwc=1:nicw=on:stl=120:sac=on:urr=on:updr=off:uhcvi=on_417");
      quick.push("dis+1011_5_add=large:anc=none:bd=preordered:cond=on:fsr=off:fde=unused:lma=on:nwc=1:sos=theory:sp=occurrence:updr=off_1327");
    }
    else {
      quick.push("dis-11_32_av=off:bs=unit_only:gs=on:irw=on:lma=on:nwc=1:updr=off_34");
      quick.push("dis+1011_128_afp=100000:afq=1.1:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:irw=on:lma=on:nwc=1:sos=theory:sac=on:urr=on:updr=off_19");
      quick.push("fmb+10_1_av=off:fmbsr=1.6:fde=none:updr=off_16");
      quick.push("lrs+4_6_afp=10000:afq=1.2:amm=sco:anc=all_dependent:bs=on:bsr=on:fde=unused:irw=on:lma=on:nwc=1:stl=30:sos=theory:sp=occurrence:uhcvi=on_264");
      quick.push("lrs+1_8:1_add=off:anc=none:bd=preordered:br=off:bce=on:fsr=off:fde=none:nwc=1:nicw=on:stl=90:sos=theory:sp=reverse_arity:urr=on_815");
      quick.push("lrs+1_5:1_add=off:afr=on:afp=4000:afq=1.1:amm=sco:anc=none:cond=on:gs=on:nwc=1.1:nicw=on:sas=z3:stl=30:sos=theory:urr=on:updr=off_178");
      quick.push("dis+4_7_aac=none:afr=on:anc=none:bd=preordered:bce=on:cond=fast:fsr=off:fde=unused:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:nicw=on:sas=z3:sac=on:sp=reverse_arity:uhcvi=on_2");
    }
    fallback.push("fmb+10_1_av=off:fmbsr=1.6:fde=none:updr=off_3000");
    fallback.push("ott+10_64_add=off:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:lcm=predicate:lma=on:nwc=1:sac=on:sp=reverse_arity:urr=on_300");
    fallback.push("lrs+2_64_add=large:afp=40000:afq=1.1:bd=off:bs=on:bsr=on:bce=on:fde=unused:irw=on:lma=on:lwlo=on:nwc=1:uhcvi=on_300");
    fallback.push("dis+4_5_afp=1000:afq=1.1:amm=off:anc=none:bd=off:gs=on:irw=on:lcm=predicate:lma=on:nwc=1:sas=z3:sos=all:sp=occurrence_300");
    fallback.push("lrs+1003_10_afp=4000:afq=1.2:amm=sco:anc=none:bd=off:bsr=on:br=off:bce=on:fde=unused:lma=on:nwc=1:nicw=on:sac=on:urr=on:updr=off:uhcvi=on_1200");
    fallback.push("dis+11_2:3_add=large:afp=10000:afq=1.2:anc=none:bd=off:bce=on:cond=fast:er=filter:fsr=off:fde=unused:gsp=on:nwc=5:sos=theory:sac=on:urr=on_300");
    fallback.push("ott-4_6_add=off:afr=on:afp=100000:afq=1.4:amm=sco:bs=on:fde=unused:gs=on:gsaa=full_model:gsem=on:irw=on:nwc=1:sas=z3:sac=on:updr=off:uhcvi=on_600");
    fallback.push("ott+11_50_aac=none:add=off:afp=1000:afq=1.4:anc=none:bs=unit_only:fde=none:gs=on:gsem=off:lma=on:nwc=1:sas=z3:sac=on:uhcvi=on_200");
    fallback.push("dis-11_32_av=off:bs=unit_only:gs=on:irw=on:lma=on:nwc=1:updr=off_300");
    fallback.push("ott+1_3_awrs=converge:awrsf=16:av=off:bd=off:bs=on:bce=on:cond=fast:gs=on:gsem=off:irw=on:lma=on:nwc=1.5:sas=z3:sp=weighted_frequency:updr=off:uhcvi=on_300");
    fallback.push("ott+1_3_add=large:afp=10000:afq=1.4:amm=off:bd=preordered:bs=on:bsr=on:bce=on:cond=fast:fsr=off:fde=unused:gs=on:irw=on:lma=on:nwc=1:sas=z3:sp=reverse_arity:updr=off:uhcvi=on_300");
    fallback.push("lrs+1_5:1_add=off:afr=on:afp=4000:afq=1.1:amm=sco:anc=none:cond=on:gs=on:nwc=1.1:nicw=on:sas=z3:sos=theory:urr=on:updr=off_300");
    fallback.push("ott+10_1_add=large:afp=1000:afq=1.2:amm=off:anc=none:bd=off:bs=on:fsr=off:gs=on:gsem=on:irw=on:lma=on:nwc=1:sas=z3:sp=occurrence:updr=off_300");
    fallback.push("dis-4_4_add=large:afr=on:afp=1000:afq=1.4:anc=all_dependent:bs=unit_only:fde=none:gs=on:gsaa=from_current:lma=on:nwc=1.2:sac=on:updr=off_600");
    fallback.push("lrs+1_16_add=off:afp=100000:afq=1.0:amm=off:cond=fast:er=filter:lcm=predicate:lma=on:lwlo=on:nwc=2:nicw=on:sd=7:ss=axioms:st=5.0:sos=theory:sp=reverse_arity:urr=ec_only_600");
    fallback.push("lrs+1_8:1_add=off:anc=none:bd=preordered:br=off:bce=on:fsr=off:fde=none:nwc=1:nicw=on:sos=theory:sp=reverse_arity:urr=on_900");
    fallback.push("dis+4_2_add=large:afr=on:afp=4000:afq=1.2:anc=none:bd=preordered:bce=on:fsr=off:fde=unused:lma=on:nwc=1:sos=all:sac=on:sp=reverse_arity:updr=off_2100");
    return;

  case Property::FEQ:
    if (atoms > 1000000) {
      quick.push("dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1200");
      quick.push("dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_1");
    }
    else if (atoms > 500000) {
      quick.push("dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_188");
      quick.push("ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=on:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_105");
      quick.push("lrs+10_5:4_av=off:cond=on:fde=unused:gs=on:gsem=on:lcm=reverse:lma=on:lwlo=on:nm=32:nwc=1.7:stl=30:sd=2:ss=axioms:st=2.0:sos=all_119");
      quick.push("dis+11_8_add=off:afp=10000:afq=1.2:amm=off:anc=none:cond=fast:ep=R:gs=on:gsaa=from_current:gsem=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=4:sd=1:ss=axioms:sac=on:updr=off:uhcvi=on_61");
      quick.push("ott+11_3_afp=1000:afq=2.0:anc=none:fsr=off:irw=on:nwc=1.7:ss=axioms:st=1.5:sac=on:updr=off_137");
      quick.push("lrs-10_3:2_add=large:afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=RST:fsr=off:fde=unused:gsp=on:gs=on:gsem=on:lma=on:nm=16:nwc=1.3:stl=30:sd=2:ss=axioms:st=5.0:sos=on:uhcvi=on_78");
      quick.push("lrs+1002_8:1_av=off:cond=on:gsp=on:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_137");
      quick.push("dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=on:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_169");
      quick.push("lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_66");
      quick.push("ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=on:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_136");
      quick.push("lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=on:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_65");
      quick.push("lrs+1002_2:1_acc=on:add=large:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:ccuc=first:fsr=off:gs=on:irw=on:nm=32:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:sos=on:sp=reverse_arity_58");
      quick.push("dis+1003_64_add=off:afr=on:afp=100000:afq=1.1:anc=none:cond=fast:fde=none:irw=on:nm=6:newcnf=on:nwc=1.3:uhcvi=on_199");
    }
    else if (atoms > 240000) {
      quick.push("lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_38");
      quick.push("lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=on:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42");
      quick.push("lrs+1002_8:1_av=off:cond=on:gsp=on:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_30");
      quick.push("ott+11_2:1_add=off:afp=10000:afq=1.1:anc=none:cond=on:gsp=on:lcm=reverse:lwlo=on:nm=32:nwc=5:sp=occurrence:updr=off_291");
      quick.push("dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_63");
      quick.push("lrs+1002_3_aac=none:acc=on:add=off:afp=4000:afq=1.1:amm=sco:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=32:newcnf=on:nwc=1.1:nicw=on:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=occurrence:updr=off_26");
      quick.push("lrs-1_5:4_add=off:afp=100000:afq=1.4:amm=sco:anc=all_dependent:fde=none:gs=on:irw=on:lma=on:nm=0:nwc=1:stl=30:sd=2:ss=axioms:sos=all:urr=ec_only_42");
      quick.push("lrs-10_3:2_add=large:afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=RST:fsr=off:fde=unused:gsp=on:gs=on:gsem=on:lma=on:nm=16:nwc=1.3:stl=30:sd=2:ss=axioms:st=5.0:sos=on:uhcvi=on_54");
      quick.push("lrs+1_4_afp=100000:afq=1.2:anc=none:bd=off:cond=on:gs=on:gsem=off:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=2.0:sos=all:updr=off_294");
      quick.push("dis+10_4_add=off:afr=on:afp=1000:afq=1.4:amm=sco:anc=none:fsr=off:gs=on:gsem=on:lcm=predicate:lma=on:nm=64:nwc=1:sd=3:ss=axioms:sos=on:sp=reverse_arity_42");
      quick.push("dis+11_3:1_add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:bd=off:bs=unit_only:irw=on:lcm=predicate:lma=on:nm=2:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence:updr=off_39");
      quick.push("lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_44");
      quick.push("dis+4_4_av=off:fsr=off:gs=on:lcm=reverse:lma=on:nm=4:newcnf=on:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence_175");
      quick.push("lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=on:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_1");
      quick.push("lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=on:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_63");
      quick.push("dis+1011_3_afp=100000:afq=1.1:amm=off:anc=none:fsr=off:gsp=on:gs=on:irw=on:nm=6:nwc=1:sas=z3:sd=2:ss=axioms:sos=on:sac=on:sp=reverse_arity:updr=off_45");
      quick.push("dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=on:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_213");
      quick.push("dis+10_5_av=off:cond=on:gs=on:gsem=off:irw=on:lcm=predicate:lma=on:lwlo=on:nm=6:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence_92");
    }
    else if (atoms > 200000) {
      quick.push("lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_33");
      quick.push("lrs+1002_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:cond=fast:fde=none:gs=on:gsem=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence_27");
      quick.push("lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=on:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_107");
      quick.push("lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=on:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_37");
      quick.push("lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_50");
      quick.push("dis+10_5_av=off:bce=on:cond=on:gsp=on:gs=on:lcm=predicate:lma=on:nm=6:nwc=1:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_30");
      quick.push("dis+11_8:1_afp=100000:afq=1.2:amm=off:anc=none:cond=on:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=1:sd=1:ss=axioms:sp=occurrence:urr=on_20");
      quick.push("lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_40");
      quick.push("lrs+1_7_av=off:cond=fast:fde=none:gs=on:gsem=off:lcm=predicate:nm=6:nwc=1:stl=30:sd=3:ss=axioms:sos=on:sp=occurrence:updr=off_23");
      quick.push("lrs-2_3:2_av=off:bce=on:cond=on:gsp=on:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_147");
      quick.push("ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_251");
      quick.push("dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_127");
      quick.push("ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=on:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_155");
      quick.push("lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_165");
      quick.push("dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_247");
    }
    else if (atoms > 130000) {
      quick.push("lrs+11_3_av=off:cond=on:er=filter:fsr=off:gsp=on:gs=on:gsem=off:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=5:ss=axioms:st=3.0:sp=reverse_arity:urr=ec_only_25");
      quick.push("lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_16");
      quick.push("lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_58");
      quick.push("lrs+1002_8:1_av=off:cond=on:gsp=on:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_30");
      quick.push("lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_25");
      quick.push("lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_32");
      quick.push("dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_24");
      quick.push("lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=on:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_22");
      quick.push("dis+4_4_av=off:fsr=off:gs=on:lcm=reverse:lma=on:nm=4:newcnf=on:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence_14");
      quick.push("dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_28");
      quick.push("lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_14");
      quick.push("ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=on:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_19");
      quick.push("dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=on:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_39");
      quick.push("lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_24");
      quick.push("lrs+11_50_afp=100000:afq=1.1:amm=sco:anc=none:bs=unit_only:cond=on:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sp=reverse_arity_252");
      quick.push("lrs+1_4_afp=100000:afq=1.2:anc=none:bd=off:cond=on:gs=on:gsem=off:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=2.0:sos=all:updr=off_290");
      quick.push("ott+2_40_av=off:bs=unit_only:bsr=on:cond=fast:ep=RST:lma=on:nm=16:nwc=1:sp=reverse_arity_177");
      quick.push("dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_33");
      quick.push("lrs-10_3:2_add=large:afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=RST:fsr=off:fde=unused:gsp=on:gs=on:gsem=on:lma=on:nm=16:nwc=1.3:stl=30:sd=2:ss=axioms:st=5.0:sos=on:uhcvi=on_301");
      quick.push("dis+10_4_add=off:afr=on:afp=1000:afq=1.4:amm=sco:anc=none:fsr=off:gs=on:gsem=on:lcm=predicate:lma=on:nm=64:nwc=1:sd=3:ss=axioms:sos=on:sp=reverse_arity_17");
      quick.push("lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_32");
      quick.push("ott+11_8_amm=off:anc=none:bsr=on:cond=on:irw=on:nm=2:nwc=1.1:ss=axioms:st=2.0:sac=on_39");
      quick.push("ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=on:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_48");
      quick.push("lrs+1002_2:1_acc=on:add=large:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:ccuc=first:fsr=off:gs=on:irw=on:nm=32:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:sos=on:sp=reverse_arity_272");
      quick.push("lrs+10_5:4_av=off:cond=on:fde=unused:gs=on:gsem=on:lcm=reverse:lma=on:lwlo=on:nm=32:nwc=1.7:stl=30:sd=2:ss=axioms:st=2.0:sos=all_172");
    }
    else if (atoms > 50000) {
      quick.push("dis+4_4_av=off:fsr=off:gs=on:lcm=reverse:lma=on:nm=4:newcnf=on:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence_8");
      quick.push("lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_21");
      quick.push("dis+1003_64_add=off:afr=on:afp=100000:afq=1.1:anc=none:cond=fast:fde=none:irw=on:nm=6:newcnf=on:nwc=1.3:uhcvi=on_7");
      quick.push("ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_60");
      quick.push("lrs+1002_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:cond=fast:fde=none:gs=on:gsem=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence_11");
      quick.push("dis+1011_3_afp=100000:afq=1.1:amm=off:anc=none:fsr=off:gsp=on:gs=on:irw=on:nm=6:nwc=1:sas=z3:sd=2:ss=axioms:sos=on:sac=on:sp=reverse_arity:updr=off_7");
      quick.push("ott+1002_128_av=off:bd=off:bs=on:bsr=on:cond=on:fsr=off:nm=6:newcnf=on:nwc=1:sp=reverse_arity:updr=off_82");
      quick.push("lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_15");
      quick.push("dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=on:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_10");
      quick.push("lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=on:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_88");
      quick.push("lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=on:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_16");
      quick.push("lrs+1002_8:1_av=off:cond=on:gsp=on:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_13");
      quick.push("dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_10");
      quick.push("lrs-1_5:4_add=off:afp=100000:afq=1.4:amm=sco:anc=all_dependent:fde=none:gs=on:irw=on:lma=on:nm=0:nwc=1:stl=30:sd=2:ss=axioms:sos=all:urr=ec_only_23");
      quick.push("lrs+1_4_afp=100000:afq=1.2:anc=none:bd=off:cond=on:gs=on:gsem=off:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=2.0:sos=all:updr=off_16");
      quick.push("lrs-10_3:2_add=large:afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=RST:fsr=off:fde=unused:gsp=on:gs=on:gsem=on:lma=on:nm=16:nwc=1.3:stl=30:sd=2:ss=axioms:st=5.0:sos=on:uhcvi=on_10");
      quick.push("dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_122");
      quick.push("lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=on:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_29");
      quick.push("lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12");
      quick.push("dis+10_5_av=off:bce=on:cond=on:gsp=on:gs=on:lcm=predicate:lma=on:nm=6:nwc=1:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_11");
      quick.push("lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_76");
      quick.push("dis-1_4_aac=none:acc=on:add=off:afr=on:afp=40000:afq=1.2:amm=off:anc=none:fsr=off:gsp=on:gs=on:lcm=predicate:lma=on:nm=6:nwc=1:sd=2:ss=axioms:sos=all:sac=on:sp=occurrence:updr=off_26");
      quick.push("ott+1010_5:4_av=off:bd=off:fde=none:irw=on:lma=on:nm=32:nwc=2.5:sd=2:ss=axioms:st=3.0:urr=on_190");
      quick.push("dis-10_3:2_aac=none:afp=1000:afq=1.1:cond=on:fsr=off:lcm=reverse:lwlo=on:nm=16:nwc=1:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity:updr=off_27");
      quick.push("lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_225");
      quick.push("lrs+4_4:1_acc=on:afr=on:afp=100000:afq=1.1:amm=sco:anc=none:ccuc=first:cond=on:fsr=off:irw=on:lcm=predicate:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all_161");
      quick.push("dis+11_3:1_add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:bd=off:bs=unit_only:irw=on:lcm=predicate:lma=on:nm=2:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence:updr=off_17");
      quick.push("lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_239");
      quick.push("lrs+1002_1_av=off:er=filter:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1:stl=30:sd=3:ss=axioms:st=1.5:sos=on_13");
      quick.push("lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_115");
      quick.push("ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=on:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_88");
      quick.push("lrs+1011_50_afr=on:afp=40000:afq=1.0:amm=off:anc=all_dependent:bs=on:bsr=on:bce=on:fde=unused:gs=on:lma=on:nm=16:nwc=1.1:stl=60:sp=occurrence:updr=off_474");
      quick.push("lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_22");
      quick.push("dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_21");
      quick.push("lrs+10_5:4_av=off:cond=on:fde=unused:gs=on:gsem=on:lcm=reverse:lma=on:lwlo=on:nm=32:nwc=1.7:stl=30:sd=2:ss=axioms:st=2.0:sos=all_229");
    }
    else if (atoms > 20000) {
      quick.push("lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_4");
      quick.push("lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_4");
      quick.push("ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=on:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_7");
      quick.push("ott+1002_128_av=off:bd=off:bs=on:bsr=on:cond=on:fsr=off:nm=6:newcnf=on:nwc=1:sp=reverse_arity:updr=off_62");
      quick.push("lrs+1_4_afp=100000:afq=1.2:anc=none:bd=off:cond=on:gs=on:gsem=off:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=2.0:sos=all:updr=off_7");
      quick.push("dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_6");
      quick.push("dis+10_5_av=off:cond=on:gs=on:gsem=off:irw=on:lcm=predicate:lma=on:lwlo=on:nm=6:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence_6");
      quick.push("ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_11");
      quick.push("ott+11_8_amm=off:anc=none:bsr=on:cond=on:irw=on:nm=2:nwc=1.1:ss=axioms:st=2.0:sac=on_8");
      quick.push("lrs+11_4:1_av=off:bd=off:br=off:cond=fast:fde=unused:irw=on:lcm=reverse:lma=on:lwlo=on:nm=4:nwc=1:stl=60:sd=3:ss=axioms:sos=all:urr=on_69");
      quick.push("lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_12");
      quick.push("lrs+1011_1_av=off:cond=on:gs=on:lma=on:nm=4:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity:updr=off_118");
      quick.push("lrs+4_1_acc=on:afr=on:afp=100000:afq=1.2:amm=sco:anc=none:bd=off:bs=on:bsr=on:ccuc=first:fsr=off:fde=unused:irw=on:lma=on:nm=0:nwc=1.3:stl=30:sd=10:ss=axioms:st=3.0:sos=all:sp=occurrence:uhcvi=on_26");
      quick.push("ott+2_8:1_aac=none:acc=on:add=large:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:bsr=on:fsr=off:lcm=predicate:lma=on:nm=2:nwc=1.7:sd=3:ss=axioms:sos=on:sp=occurrence:updr=off_12");
      quick.push("lrs+1011_50_afr=on:afp=40000:afq=1.0:amm=off:anc=all_dependent:bs=on:bsr=on:bce=on:fde=unused:gs=on:lma=on:nm=16:nwc=1.1:stl=60:sp=occurrence:updr=off_83");
    }
    else if (prop == 2ul) {
      quick.push("lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136");
      quick.push("lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123");
      quick.push("dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13");
      quick.push("lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75");
      quick.push("dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3");
      quick.push("ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10");
      quick.push("dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10");
      quick.push("ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294");
      quick.push("lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520");
      quick.push("lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461");
      quick.push("ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385");
      quick.push("dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122");
      quick.push("dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16");
      quick.push("ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052");
      quick.push("lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236");
      quick.push("ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355");
      quick.push("ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883");
      quick.push("lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893");
    }
    else if (prop == 0ul) {
      if (atoms > 21) {
        quick.push("lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18");
        quick.push("lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51");
        quick.push("lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118");
        quick.push("dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22");
        quick.push("lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63");
        quick.push("lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=on:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20");
        quick.push("lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=on:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42");
        quick.push("dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2");
        quick.push("lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71");
        quick.push("lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142");
        quick.push("lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12");
        quick.push("lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136");
        quick.push("dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2");
        quick.push("lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207");
        quick.push("lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18");
        quick.push("ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122");
        quick.push("ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19");
        quick.push("dis+11_1_av=off:gsp=on:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246");
        quick.push("lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174");
        quick.push("lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426");
        quick.push("lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=on:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172");
        quick.push("ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70");
        quick.push("dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398");
        quick.push("lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=on:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412");
      }
      else {
        quick.push("lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6");
        quick.push("lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3");
        quick.push("lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79");
        quick.push("lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=on:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99");
        quick.push("lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61");
        quick.push("ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102");
        quick.push("lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214");
        quick.push("ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=on:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389");
        quick.push("lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211");
        quick.push("ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420");
        quick.push("ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823");
        quick.push("lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759");
      }
    }
    else if (prop == 131072ul) {
      quick.push("lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2");
      quick.push("lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2");
      quick.push("lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7");
      quick.push("dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9");
      quick.push("lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11");
      quick.push("dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2");
      quick.push("lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38");
      quick.push("lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12");
      quick.push("lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3");
      quick.push("lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5");
      quick.push("dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2");
      quick.push("lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=on:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21");
      quick.push("lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2");
      quick.push("lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81");
      quick.push("lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129");
      quick.push("lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159");
      quick.push("ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=on:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45");
      quick.push("ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180");
      quick.push("lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83");
      quick.push("dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169");
      quick.push("dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3");
    }
    else if (prop == 131087ul) {
      quick.push("lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=on:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11");
      quick.push("lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=on:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21");
      quick.push("lrs+1002_8:1_av=off:cond=on:gsp=on:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41");
      quick.push("lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8");
      quick.push("dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=on:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33");
      quick.push("lrs+11_4_av=off:gsp=on:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8");
      quick.push("dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17");
      quick.push("lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6");
      quick.push("lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11");
      quick.push("ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6");
      quick.push("dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3");
      quick.push("dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34");
      quick.push("dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15");
      quick.push("dis+4_2_av=off:bs=on:fsr=off:gsp=on:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127");
      quick.push("dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4");
      quick.push("lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7");
      quick.push("lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_23");
      quick.push("lrs-2_3:2_av=off:bce=on:cond=on:gsp=on:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62");
      quick.push("lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11");
      quick.push("lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6");
      quick.push("lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49");
      quick.push("ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=on:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70");
      quick.push("dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157");
      quick.push("lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9");
      quick.push("dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9");
      quick.push("ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=on:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88");
      quick.push("dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4");
      quick.push("ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=on:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49");
      quick.push("lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4");
      quick.push("lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48");
      quick.push("dis+1011_8:1_aac=none:acc=on:afp=1000:afq=1.4:amm=off:anc=all:bs=unit_only:bce=on:ccuc=small_ones:fsr=off:fde=unused:gsp=on:gs=on:gsem=off:lma=on:nm=16:nwc=2.5:sd=4:ss=axioms:st=1.5:sos=all:uhcvi=on_65");
      quick.push("ott+1_5:1_acc=on:add=off:afr=on:afp=100000:afq=1.1:amm=sco:anc=none:lcm=predicate:nm=16:nwc=1.1:sd=1:ss=axioms:st=3.0:sos=on:sac=on:updr=off_18");
      quick.push("lrs+1002_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:cond=fast:fde=none:gs=on:gsem=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence_8");
      quick.push("dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_4");
      quick.push("lrs+1002_3:1_av=off:bd=off:cond=fast:fde=none:gsp=on:lcm=predicate:lma=on:lwlo=on:nm=4:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_134");
      quick.push("dis+10_5_av=off:bce=on:cond=on:gsp=on:gs=on:lcm=predicate:lma=on:nm=6:nwc=1:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_6");
      quick.push("lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_243");
      quick.push("ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_254");
      quick.push("lrs+10_2:3_afp=1000:afq=1.1:amm=sco:anc=none:er=known:lcm=reverse:lwlo=on:nm=64:newcnf=on:nwc=2:stl=30:sd=5:ss=axioms:sos=theory:sac=on:sp=occurrence_78");
      quick.push("lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_27");
      quick.push("lrs-2_3:1_add=off:afr=on:afp=1000:afq=1.2:amm=sco:anc=all_dependent:bd=off:bs=unit_only:bsr=on:cond=on:fde=unused:gs=on:gsem=on:irw=on:lcm=reverse:nm=32:nwc=1.7:sas=z3:stl=30:sos=all:sac=on_28");
      quick.push("lrs+1002_2:1_acc=on:add=large:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:ccuc=first:fsr=off:gs=on:irw=on:nm=32:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:sos=on:sp=reverse_arity_3");
      quick.push("dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_4");
      quick.push("ott-11_3_av=off:bsr=on:cond=fast:fde=unused:lcm=predicate:lma=on:nm=6:nwc=1:sos=on:updr=off_546");
      quick.push("dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=on:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_138");
      quick.push("lrs+11_8:1_av=off:bd=preordered:br=off:cond=on:gs=on:gsem=on:lcm=reverse:lma=on:nm=0:nwc=1:stl=60:urr=on_362");
      quick.push("ott+1004_12_awrs=converge:awrsf=64:aac=none:afr=on:afp=4000:afq=1.4:amm=sco:anc=none:bs=on:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=on:lma=on:nwc=5:nicw=on:sas=z3:sos=all:sac=on:sp=occurrence:urr=ec_only_113");
      quick.push("lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_41");
      quick.push("dis+1010_128_afr=on:afp=10000:afq=1.1:anc=none:bsr=on:br=off:bce=on:cond=on:fsr=off:gsp=on:irw=on:nm=6:newcnf=on:nwc=1.5:sos=all:sac=on:sp=occurrence:urr=on:updr=off_107");
      quick.push("lrs+1002_8:1_add=large:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:bsr=on:er=known:lwlo=on:nm=0:nwc=1.2:stl=30:sd=1:ss=axioms:sp=occurrence:updr=off_51");
    }
    else if (prop == 131075ul) {
      quick.push("dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=on:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8");
      quick.push("dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4");
      quick.push("dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=on:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1");
      quick.push("dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5");
      quick.push("dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89");
      quick.push("dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9");
      quick.push("dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2");
      quick.push("lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3");
      quick.push("lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23");
      quick.push("lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66");
      quick.push("dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=on:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217");
      quick.push("lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23");
      quick.push("lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6");
      quick.push("dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83");
      quick.push("lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2");
      quick.push("dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17");
      quick.push("dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9");
      quick.push("lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36");
      quick.push("ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88");
      quick.push("lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24");
      quick.push("ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13");
      quick.push("dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75");
      quick.push("lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223");
      quick.push("dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83");
      quick.push("dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1");
      quick.push("lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91");
      quick.push("lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11");
      quick.push("lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6");
      quick.push("dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=on:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73");
      quick.push("lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2");
      quick.push("ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239");
      quick.push("dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155");
      quick.push("lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4");
      quick.push("lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25");
      quick.push("dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=on:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171");
      quick.push("dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99");
      quick.push("lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3");
      quick.push("dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24");
      quick.push("lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=on:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22");
      quick.push("ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4");
      quick.push("lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=on:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95");
      quick.push("lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80");
      quick.push("lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98");
      quick.push("lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1");
      quick.push("lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=on:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298");
      quick.push("lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1");
      quick.push("ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2");
      quick.push("lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=on:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1");
      quick.push("lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97");
      quick.push("dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1");
      quick.push("lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1");
    }
    else if (prop == 131073ul) {
      if (atoms > 150) {
        quick.push("ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_3");
        quick.push("dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_2");
        quick.push("ott+1010_5:4_av=off:bd=off:fde=none:irw=on:lma=on:nm=32:nwc=2.5:sd=2:ss=axioms:st=3.0:urr=on_5");
        quick.push("lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_3");
        quick.push("lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2");
        quick.push("dis+1011_10_aac=none:add=large:afp=10000:afq=1.1:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=6:newcnf=on:nwc=2.5:sp=reverse_arity:updr=off_2");
        quick.push("ott+1002_2_av=off:bd=preordered:irw=on:lma=on:nm=64:nwc=10:sp=reverse_arity:updr=off_22");
        quick.push("lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_16");
        quick.push("dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_4");
        quick.push("dis+11_4_afr=on:afp=1000:afq=1.4:amm=off:anc=none:lcm=reverse:lma=on:lwlo=on:nm=6:newcnf=on:nwc=1:sd=2:ss=axioms:st=2.0:sp=reverse_arity_2");
        quick.push("dis-3_5_av=off:cond=on:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1:sos=on:sp=reverse_arity_3");
        quick.push("lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_5");
        quick.push("lrs+1003_2_acc=on:afp=4000:afq=2.0:amm=sco:bd=off:ccuc=small_ones:fsr=off:fde=unused:gsp=on:nm=64:newcnf=on:nwc=2.5:nicw=on:stl=30:urr=ec_only_8");
        quick.push("lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=on:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_14");
        quick.push("ott+1_8_av=off:bd=off:bs=on:cond=on:gsp=on:gs=on:gsem=off:irw=on:lcm=predicate:lwlo=on:nwc=1:sos=on_10");
        quick.push("dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_4");
        quick.push("dis+11_3:1_add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:bd=off:bs=unit_only:irw=on:lcm=predicate:lma=on:nm=2:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence:updr=off_1");
        quick.push("lrs+1002_3_aac=none:acc=on:add=off:afp=4000:afq=1.1:amm=sco:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=32:newcnf=on:nwc=1.1:nicw=on:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=occurrence:updr=off_24");
        quick.push("dis+1010_4_afp=10000:afq=1.2:anc=none:irw=on:lma=on:nm=64:nwc=10:sas=z3:sac=on:sp=reverse_arity:updr=off_2");
        quick.push("lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_36");
        quick.push("ott+1004_12_awrs=converge:awrsf=64:aac=none:afr=on:afp=4000:afq=1.4:amm=sco:anc=none:bs=on:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=on:lma=on:nwc=5:nicw=on:sas=z3:sos=all:sac=on:sp=occurrence:urr=ec_only_2");
        quick.push("dis+11_28_av=off:fsr=off:irw=on:lcm=predicate:nm=2:newcnf=on:nwc=5:sp=occurrence:urr=on:updr=off_2");
        quick.push("dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_72");
        quick.push("dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2");
        quick.push("lrs+1011_4:1_av=off:fsr=off:irw=on:nwc=1:stl=30:sd=4:ss=axioms:st=1.5:sp=reverse_arity_12");
        quick.push("dis+11_5_av=off:bd=off:bs=unit_only:bsr=on:cond=on:lcm=reverse:nm=0:nwc=1.2_5");
        quick.push("ott+1002_128_av=off:bd=off:bs=on:bsr=on:cond=on:fsr=off:nm=6:newcnf=on:nwc=1:sp=reverse_arity:updr=off_9");
        quick.push("dis+1003_64_add=off:afr=on:afp=100000:afq=1.1:anc=none:cond=fast:fde=none:irw=on:nm=6:newcnf=on:nwc=1.3:uhcvi=on_5");
        quick.push("lrs+10_6_aac=none:acc=model:add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bd=off:ccuc=small_ones:irw=on:lcm=reverse:nm=0:nwc=1:nicw=on:stl=30:sos=on:sp=reverse_arity:updr=off_2");
        quick.push("ott+11_8_amm=off:anc=none:bsr=on:cond=on:irw=on:nm=2:nwc=1.1:ss=axioms:st=2.0:sac=on_1");
        quick.push("lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_4");
        quick.push("lrs+10_1_afr=on:afp=100000:afq=1.2:amm=sco:anc=none:br=off:cond=on:gs=on:gsem=on:irw=on:nm=16:nwc=1:stl=30:sac=on:sp=occurrence:urr=on:updr=off_12");
        quick.push("ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_17");
        quick.push("lrs+10_2:3_afp=1000:afq=1.1:amm=sco:anc=none:er=known:lcm=reverse:lwlo=on:nm=64:newcnf=on:nwc=2:stl=30:sd=5:ss=axioms:sos=theory:sac=on:sp=occurrence_233");
        quick.push("dis+11_32_av=off:ep=RST:fsr=off:lwlo=on:nm=6:nwc=1.1:sd=5:ss=axioms:st=5.0:sp=reverse_arity:uhcvi=on_2");
        quick.push("ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_125");
        quick.push("ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_205");
        quick.push("lrs+1011_2:1_av=off:irw=on:lwlo=on:nm=16:newcnf=on:nwc=2:stl=30:sd=4:ss=axioms:st=3.0:sp=occurrence_30");
        quick.push("dis+1002_8_add=large:afp=100000:afq=1.2:amm=off:bs=on:irw=on:nm=2:newcnf=on:nwc=1.1:sos=on:sp=reverse_arity:urr=ec_only:updr=off_259");
        quick.push("lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_5");
        quick.push("dis+11_10_av=off:lma=on:nm=64:nwc=5:sp=reverse_arity_3");
        quick.push("ott-11_12_aac=none:afp=100000:afq=1.2:amm=sco:bs=on:bce=on:cond=fast:er=known:gs=on:gsaa=from_current:gsem=off:irw=on:nm=4:nwc=2:sas=z3:sos=all:sp=occurrence:urr=ec_only:updr=off_253");
        quick.push("ott+10_2:3_add=large:afp=40000:afq=1.1:amm=off:anc=all_dependent:bd=preordered:bs=unit_only:cond=fast:er=filter:gs=on:gsaa=from_current:lma=on:nm=32:nwc=1.1:sas=z3:sac=on:sp=occurrence:urr=ec_only:updr=off_679");
        quick.push("lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_21");
        quick.push("lrs+10_128_acc=model:afp=100000:afq=2.0:anc=all_dependent:bs=on:bsr=on:cond=fast:er=filter:gs=on:gsem=off:lcm=reverse:lma=on:nm=32:nwc=3:stl=30:sac=on:sp=occurrence:urr=ec_only_70");
        quick.push("lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_51");
        quick.push("lrs+1010_5:4_av=off:bd=off:bsr=on:irw=on:lwlo=on:newcnf=on:nwc=1.1:stl=90:sos=all:sp=occurrence:uhcvi=on_145");
        quick.push("lrs+11_4_av=off:gsp=on:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_59");
        quick.push("lrs+1011_14_av=off:fsr=off:irw=on:nwc=1:stl=30:sos=on:sp=occurrence:urr=ec_only:updr=off_53");
        quick.push("dis+11_5_afp=40000:afq=1.4:anc=none:br=off:cond=on:fsr=off:irw=on:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=2.0:urr=on:updr=off_5");
        quick.push("lrs+1_3:2_aac=none:add=large:anc=all_dependent:bce=on:cond=fast:ep=RST:fsr=off:lma=on:nm=2:nwc=1:stl=30:sos=on:sp=occurrence:urr=on:updr=off:uhcvi=on_5");
        quick.push("lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_3");
        quick.push("dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_158");
      }
      else {
        quick.push("dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2");
        quick.push("dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=on:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6");
        quick.push("dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=on:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105");
        quick.push("lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92");
        quick.push("dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7");
        quick.push("lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=on:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27");
        quick.push("lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3");
        quick.push("lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32");
        quick.push("dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5");
        quick.push("lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85");
        quick.push("lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42");
        quick.push("lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48");
        quick.push("ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=on:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197");
        quick.push("ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=on:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2");
        quick.push("dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2");
        quick.push("lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162");
        quick.push("lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230");
        quick.push("lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145");
        quick.push("dis+1010_3:1_av=off:gsp=on:nm=6:nwc=1:sos=all:sp=occurrence_48");
        quick.push("lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220");
        quick.push("dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=on:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34");
        quick.push("dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98");
        quick.push("lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285");
        quick.push("ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104");
        quick.push("dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288");
        quick.push("lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364");
      }
    }
    else {
      quick.push("lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2");
      quick.push("lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2");
      quick.push("dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6");
      quick.push("dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39");
      quick.push("lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10");
      quick.push("lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1");
      quick.push("ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14");
      quick.push("lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3");
      quick.push("ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=on:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18");
      quick.push("lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34");
      quick.push("lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2");
      quick.push("lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11");
      quick.push("lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2");
      quick.push("lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=on:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22");
      quick.push("lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13");
      quick.push("lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9");
      quick.push("dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=on:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3");
      quick.push("ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2");
      quick.push("ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14");
      quick.push("lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19");
      quick.push("lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126");
      quick.push("dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4");
      quick.push("dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=on:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8");
      quick.push("ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197");
      quick.push("lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9");
      quick.push("dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111");
      quick.push("lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=on:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8");
      quick.push("dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10");
      quick.push("lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=on:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3");
      quick.push("dis+1010_3:2_av=off:gsp=on:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29");
      quick.push("lrs+11_1_av=off:bsr=on:gsp=on:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245");
      quick.push("lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20");
      quick.push("dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12");
      quick.push("ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1");
      quick.push("dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1");
      quick.push("lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100");
      quick.push("dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=on:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8");
      quick.push("lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41");
      quick.push("lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12");
      quick.push("dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143");
      quick.push("lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78");
      quick.push("dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96");
      quick.push("dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2");
      quick.push("lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113");
      quick.push("lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26");
      quick.push("dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=on:irw=on:nm=16:nwc=1:sos=all_8");
      quick.push("dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1");
      quick.push("ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111");
      quick.push("lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9");
      quick.push("lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1");
      quick.push("ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=on:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44");
      quick.push("lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73");
      quick.push("ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275");
      quick.push("lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117");
      quick.push("ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1");
      quick.push("dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180");
      quick.push("lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1");
      quick.push("ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34");
    }
    break;

  case Property::FNE:
    if (atoms > 1000) {
      quick.push("dis+11_3_afr=on:afp=4000:afq=1.4:anc=none:cond=on:fsr=off:gs=on:lcm=reverse:nm=64:nwc=1:sos=on:sp=reverse_arity_3");
      quick.push("dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_75");
      quick.push("lrs+1011_1024_add=large:afp=4000:afq=1.1:anc=none:br=off:fsr=off:gsp=on:lma=on:nwc=1:stl=30:sos=on:urr=on_187");
      quick.push("dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_52");
      quick.push("dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_481");
      quick.push("lrs+1011_40_add=off:afr=on:afp=4000:afq=1.2:amm=sco:cond=on:fsr=off:gsp=on:gs=on:gsaa=from_current:gsem=off:nm=64:nwc=1:stl=60:sos=all:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_388");
      quick.push("ott+11_3:2_afp=40000:afq=1.0:amm=sco:bs=unit_only:cond=on:fsr=off:gs=on:gsaa=full_model:lcm=reverse:nm=32:newcnf=on:nwc=5:nicw=on:sd=3:ss=axioms:sac=on:urr=on:updr=off_1019");
    }
    else {
      quick.push("dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2");
      quick.push("dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7");
      quick.push("lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3");
      quick.push("lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3");
      quick.push("dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12");
      quick.push("dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=on:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12");
      quick.push("dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=on:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191");
      quick.push("dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3");
      quick.push("lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2");
      quick.push("dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91");
      quick.push("lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73");
      quick.push("dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4");
      quick.push("lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81");
      quick.push("dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2");
      quick.push("lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152");
      quick.push("ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81");
      quick.push("dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=on:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670");
      quick.push("ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287");
      quick.push("lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2");
      quick.push("lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733");
      quick.push("dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=on:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33");
    }
    break;

  case Property::NEQ:
    if (prop == 1) {
      quick.push("lrs+1011_2_acc=on:add=off:afp=100000:afq=1.0:amm=sco:anc=none:bd=off:er=known:nwc=4:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off_2");
      quick.push("dis+10_10_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:gs=on:gsem=off:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2");
      quick.push("dis+1011_12_av=off:bd=off:bs=unit_only:fsr=off:lma=on:nwc=1:urr=ec_only:updr=off_18");
      quick.push("lrs+11_5_av=off:cond=on:gs=on:gsem=on:irw=on:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sp=occurrence:urr=on_4");
      quick.push("lrs+11_2_afr=on:afp=100000:afq=1.4:amm=off:gsp=on:gs=on:gsem=off:lcm=reverse:nwc=1:stl=30:sos=on:updr=off_3");
      quick.push("dis+11_4_aac=none:add=large:afp=100000:afq=1.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:lcm=reverse:lma=on:nwc=1:sos=all:sac=on:sp=reverse_arity:urr=ec_only_3");
      quick.push("lrs-11_10_afr=on:afp=1000:afq=1.0:amm=off:anc=none:gs=on:irw=on:lma=on:nwc=2.5:stl=30:sac=on:sp=reverse_arity:urr=on:updr=off_7");
      quick.push("dis+1011_2:1_av=off:lma=on:nwc=1:sd=3:ss=axioms:st=5.0:sp=occurrence:urr=ec_only_30");
      quick.push("lrs+10_3_av=off:bd=off:cond=on:gs=on:gsem=off:irw=on:lwlo=on:nwc=1.2:stl=30:sp=reverse_arity:updr=off_72");
      quick.push("lrs+10_12_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=off:cond=on:er=filter:lcm=predicate:lma=on:lwlo=on:nwc=1.3:sas=z3:stl=30:sac=on_71");
      quick.push("dis+1010_3:1_aac=none:add=large:afp=100000:afq=1.1:amm=sco:anc=none:bd=off:fsr=off:gs=on:lma=on:nwc=1:sos=all:sp=occurrence_18");
      quick.push("lrs+11_14_av=off:bd=off:bs=unit_only:cond=on:gsp=on:gs=on:gsem=on:irw=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sos=on:sp=reverse_arity:urr=on:updr=off_46");
      quick.push("lrs+1011_3:1_add=large:afr=on:afp=40000:afq=1.2:amm=off:anc=none:bce=on:fde=unused:gs=on:gsem=off:irw=on:lwlo=on:nwc=1:stl=30:sd=3:ss=axioms:st=3.0:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_163");
      quick.push("lrs+4_2_av=off:bs=on:er=known:gs=on:irw=on:lwlo=on:nwc=10:stl=30:sp=occurrence_243");
      quick.push("lrs+11_10_aac=none:acc=on:afp=4000:afq=1.2:amm=sco:anc=none:ccuc=first:fsr=off:irw=on:nwc=2:nicw=on:stl=30:sd=5:ss=axioms:st=1.2:sos=theory:urr=ec_only:updr=off_155");
      quick.push("dis-10_3:1_add=large:afr=on:afp=1000:afq=2.0:anc=none:cond=fast:fsr=off:fde=none:gs=on:gsem=off:irw=on:lcm=reverse:lma=on:nwc=1:sas=z3:sd=2:ss=axioms:st=2.0:sos=all:sac=on:sp=reverse_arity:urr=on:uhcvi=on_84");
      quick.push("ott+10_4:1_av=off:bd=preordered:cond=fast:fde=unused:irw=on:lcm=reverse:nwc=3:sd=2:ss=axioms:st=5.0:sp=reverse_arity:uhcvi=on_41");
      quick.push("lrs+1011_3:1_av=off:bs=unit_only:bsr=on:er=known:fsr=off:fde=unused:irw=on:lcm=reverse:lwlo=on:nwc=1.7:stl=30:sos=on:sp=occurrence:updr=off_229");
      quick.push("lrs+1_20_add=large:afr=on:afp=4000:afq=1.2:amm=off:anc=none:cond=on:fsr=off:gs=on:gsem=off:lwlo=on:nwc=1:sas=z3:stl=30:sd=3:ss=axioms:st=1.2:sp=occurrence:updr=off_136");
      quick.push("dis-11_64_av=off:bd=off:bs=on:cond=on:fsr=off:nwc=1:sd=1:ss=axioms:urr=ec_only:updr=off_99");
      quick.push("lrs+11_1_av=off:bsr=on:fde=none:irw=on:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence_68");
      quick.push("dis+11_5_afr=on:afp=100000:afq=1.2:amm=sco:anc=none:cond=on:fsr=off:gs=on:gsem=off:irw=on:lma=on:nwc=1.7:sas=z3:sac=on:sp=reverse_arity:urr=ec_only:updr=off_6");
      quick.push("lrs+1011_2:1_av=off:bce=on:cond=fast:fsr=off:fde=none:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:st=3.0:sp=occurrence:urr=ec_only:updr=off_144");
      quick.push("dis+10_1_add=off:afp=4000:afq=1.4:amm=off:anc=none:cond=on:irw=on:nwc=1:sas=z3:sd=1:ss=axioms:st=3.0:sos=all:sp=occurrence_205");
      quick.push("lrs-2_2:1_afr=on:afp=1000:afq=2.0:anc=none:bd=off:bce=on:cond=fast:gs=on:gsaa=from_current:gsem=on:lwlo=on:nwc=1.5:stl=30:sac=on:sp=reverse_arity:uhcvi=on_183");
      quick.push("dis+1011_1_add=off:afp=100000:afq=1.4:anc=none:cond=on:fsr=off:gsp=on:gs=on:gsem=off:nwc=1:nicw=on:sac=on:sp=occurrence:urr=on_77");
      quick.push("dis+4_5:1_av=off:nwc=1:sos=all:sp=reverse_arity:urr=on:updr=off_53");
      quick.push("dis+10_3_acc=on:afr=on:afp=1000:afq=1.0:amm=sco:bs=unit_only:ccuc=first:fsr=off:irw=on:lcm=reverse:lma=on:nwc=1.5:updr=off_63");
    }
    else if (prop == 3) {
      quick.push("dis-11_64_av=off:bd=off:bs=on:cond=on:fsr=off:nwc=1:sd=1:ss=axioms:urr=ec_only:updr=off_1");
      quick.push("lrs+10_5:1_add=large:afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=off:lcm=predicate:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_5");
      quick.push("dis+11_3_add=off:afr=on:afp=4000:afq=2.0:amm=off:anc=none:cond=on:gs=on:gsem=off:irw=on:lma=on:lwlo=on:nwc=1:sas=z3:sos=on:sac=on:updr=off_5");
      quick.push("lrs+1011_2:1_av=off:bsr=on:cond=on:nwc=1:sas=z3:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_8");
      quick.push("lrs+2_3:2_aac=none:acc=model:add=off:afr=on:afp=10000:afq=1.4:anc=none:bs=on:bsr=on:ccuc=first:gsp=on:gs=on:gsem=off:lcm=reverse:lma=on:nwc=3:stl=30:sd=3:ss=axioms:st=2.0:sac=on:urr=on_29");
      quick.push("lrs+1004_20_av=off:cond=on:er=filter:gsp=on:gs=on:gsem=on:lcm=reverse:nwc=1:stl=30:sd=3:ss=axioms:st=3.0:sos=on:urr=ec_only_57");
      quick.push("lrs+1002_3:1_av=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity_4");
      quick.push("dis+11_5_afr=on:afp=1000:afq=1.0:amm=off:anc=none:irw=on:lcm=reverse:nwc=1:sd=1:ss=axioms:st=1.5:sos=on:sac=on:sp=occurrence_2");
      quick.push("dis+1010_1024_afr=on:afp=10000:afq=2.0:amm=off:anc=none:fsr=off:gs=on:irw=on:lwlo=on:nwc=1:sas=z3:sd=1:ss=axioms:st=3.0_3");
      quick.push("dis+2_5:4_add=large:afp=4000:afq=1.2:anc=all:bce=on:cond=fast:fde=none:lma=on:nwc=10:sd=1:ss=axioms:st=1.5:sac=on_9");
      quick.push("dis-11_4:1_amm=sco:anc=none:cond=on:fsr=off:gsp=on:lma=on:nwc=10:sac=on:sp=reverse_arity:urr=on_14");
      quick.push("dis+10_1_add=off:afp=4000:afq=1.4:amm=off:anc=none:cond=on:irw=on:nwc=1:sas=z3:sd=1:ss=axioms:st=3.0:sos=all:sp=occurrence_3");
      quick.push("lrs+1003_3_av=off:bd=off:fde=none:gs=on:lma=on:nwc=1:stl=30:sd=7:ss=axioms:st=1.2:sos=all:sp=reverse_arity:updr=off:uhcvi=on_103");
      quick.push("lrs+1_2:1_av=off:fsr=off:lma=on:nwc=1:stl=30:sd=7:ss=axioms:st=1.2:sos=on:urr=ec_only_11");
      quick.push("lrs+1010_8:1_av=off:bs=unit_only:br=off:cond=on:fsr=off:irw=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=3.0:sp=reverse_arity:urr=on:updr=off_62");
      quick.push("lrs+1011_2:1_av=off:cond=on:er=known:gs=on:gsem=on:lwlo=on:nwc=1.3:stl=30:updr=off:uhcvi=on_180");
      quick.push("lrs+1010_3:1_av=off:cond=on:nwc=5:stl=30:sp=reverse_arity_18");
      quick.push("dis+1011_3_av=off:nwc=1:sos=all:sp=reverse_arity_67");
      quick.push("lrs+1011_5:4_av=off:bd=off:fsr=off:gs=on:nwc=1.3:stl=30:urr=ec_only:updr=off_91");
      quick.push("lrs+1011_4:1_av=off:cond=on:irw=on:lma=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_124");
      quick.push("dis+1011_1_add=off:afp=100000:afq=1.4:anc=none:cond=on:fsr=off:gsp=on:gs=on:gsem=off:nwc=1:nicw=on:sac=on:sp=occurrence:urr=on_6");
      quick.push("dis-11_5:1_acc=model:add=off:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=first:cond=on:gs=on:gsem=off:nwc=1:sd=3:ss=axioms:st=1.2:sos=all_76");
      quick.push("lrs+1011_40_add=off:afp=1000:afq=2.0:anc=none:bs=unit_only:fsr=off:irw=on:nwc=1:sas=z3:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_86");
      quick.push("dis+1002_5:1_av=off:cond=fast:fsr=off:fde=none:lma=on:nwc=1:sd=3:ss=axioms:st=1.5:sos=all:urr=on:updr=off_19");
      quick.push("lrs-1_14_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:cond=on:gs=on:gsem=off:nwc=1:nicw=on:sas=z3:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=ec_only:updr=off_176");
      quick.push("lrs+1_32_av=off:bd=off:br=off:gs=on:gsem=on:irw=on:nwc=1:stl=30:sd=1:ss=axioms:sp=occurrence:urr=on:updr=off_9");
      quick.push("lrs+1011_2_av=off:bs=unit_only:bsr=on:gs=on:gsem=on:nwc=3:stl=30:updr=off_287");
      quick.push("dis+11_2_av=off:gs=on:gsem=on:irw=on:nwc=1:sd=2:ss=axioms:st=1.5:sos=all:sp=reverse_arity_6");
      quick.push("lrs+1_3_av=off:fsr=off:lma=on:nwc=1:stl=30:sd=1:ss=axioms:sp=occurrence:urr=on_22");
      quick.push("dis+11_3_av=off:bd=off:bsr=on:bce=on:gsp=on:gs=on:gsem=on:lma=on:nwc=2.5:sp=reverse_arity:urr=ec_only:uhcvi=on_205");
      quick.push("lrs-11_3_aac=none:acc=on:afr=on:afp=10000:afq=1.1:bd=off:bs=unit_only:ccuc=first:irw=on:lcm=predicate:lma=on:nwc=1.5:stl=30:sos=all:sac=on:sp=occurrence:updr=off_111");
      quick.push("lrs+1011_2:1_av=off:bce=on:cond=fast:fsr=off:fde=none:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:st=3.0:sp=occurrence:urr=ec_only:updr=off_102");
      quick.push("lrs-11_10_afr=on:afp=1000:afq=1.0:amm=off:anc=none:gs=on:irw=on:lma=on:nwc=2.5:stl=30:sac=on:sp=reverse_arity:urr=on:updr=off_168");
      quick.push("dis+1011_2:1_av=off:lma=on:nwc=1:sd=3:ss=axioms:st=5.0:sp=occurrence:urr=ec_only_154");
    }
    else {
      quick.push("dis+11_5_afr=on:afp=1000:afq=1.0:amm=off:anc=none:irw=on:lcm=reverse:nwc=1:sd=1:ss=axioms:st=1.5:sos=on:sac=on:sp=occurrence_6");
      quick.push("dis+1002_4_afr=on:afp=1000:afq=1.2:amm=off:anc=none:cond=on:gs=on:gsem=off:lma=on:nwc=1:sos=on:sac=on:sp=occurrence_45");
      quick.push("dis+1003_3_add=off:afp=100000:afq=2.0:amm=sco:anc=none:bs=on:bsr=on:bce=on:cond=fast:fde=none:gs=on:gsaa=from_current:gsem=off:nwc=1.2:sas=z3:sac=on:sp=reverse_arity_13");
      quick.push("lrs+1011_5_av=off:cond=on:er=filter:gs=on:nwc=1.7:stl=30:updr=off_3");
      quick.push("lrs+1011_2_av=off:bs=unit_only:bsr=on:gs=on:gsem=on:nwc=3:stl=30:updr=off_3");
      quick.push("lrs-11_10_afr=on:afp=1000:afq=1.0:amm=off:anc=none:gs=on:irw=on:lma=on:nwc=2.5:stl=30:sac=on:sp=reverse_arity:urr=on:updr=off_8");
      quick.push("lrs+1011_3:1_av=off:bs=unit_only:bsr=on:er=known:fsr=off:fde=unused:irw=on:lcm=reverse:lwlo=on:nwc=1.7:stl=30:sos=on:sp=occurrence:updr=off_3");
      quick.push("lrs+1011_2_acc=on:add=off:afp=100000:afq=1.0:amm=sco:anc=none:bd=off:er=known:nwc=4:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off_13");
      quick.push("lrs+10_5:1_add=large:afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=off:lcm=predicate:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_5");
      quick.push("ott+1011_2:3_av=off:cond=fast:er=filter:fde=unused:gsp=on:irw=on:nwc=3:sp=occurrence:updr=off:uhcvi=on_4");
      quick.push("dis+11_3_add=off:afr=on:afp=4000:afq=2.0:amm=off:anc=none:cond=on:gs=on:gsem=off:irw=on:lma=on:lwlo=on:nwc=1:sas=z3:sos=on:sac=on:updr=off_79");
      quick.push("lrs+10_2:1_av=off:bsr=on:cond=on:er=known:irw=on:lcm=predicate:nwc=4:stl=30:sp=occurrence_3");
      quick.push("dis+2_3_av=off:cond=on:fsr=off:lcm=reverse:lma=on:nwc=1:sos=on:sp=reverse_arity_6");
      quick.push("lrs+11_2_afr=on:afp=100000:afq=1.4:amm=off:gsp=on:gs=on:gsem=off:lcm=reverse:nwc=1:stl=30:sos=on:updr=off_5");
      quick.push("lrs+11_1_av=off:bsr=on:fde=none:irw=on:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence_100");
      quick.push("dis+11_3_afp=100000:afq=1.1:amm=sco:anc=none:fsr=off:gs=on:gsem=on:irw=on:lma=on:nwc=10:sac=on_17");
      quick.push("lrs+11_1_av=off:fsr=off:irw=on:lma=on:lwlo=on:nwc=1:stl=30:sp=reverse_arity:urr=on:updr=off_44");
      quick.push("lrs+4_2_av=off:bs=on:er=known:gs=on:irw=on:lwlo=on:nwc=10:stl=30:sp=occurrence_100");
      quick.push("ott+1011_4_acc=on:add=off:afr=on:afp=100000:afq=1.0:amm=sco:anc=none:bd=off:bs=unit_only:ccuc=small_ones:cond=on:fsr=off:irw=on:lwlo=on:nwc=1.3:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_23");
      quick.push("lrs+11_5_add=large:afr=on:afp=40000:afq=1.2:cond=on:er=known:gs=on:gsem=off:nwc=1.5:stl=30:sp=occurrence:updr=off_65");
      quick.push("lrs+1011_2_av=off:bd=preordered:bs=unit_only:cond=fast:fsr=off:fde=unused:irw=on:lma=on:lwlo=on:nwc=1.2:stl=30:sp=occurrence:uhcvi=on_90");
      quick.push("ott+10_28_acc=model:add=off:afp=40000:afq=2.0:amm=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=on:fsr=off:gs=on:gsem=on:nwc=1.1:nicw=on:urr=on:updr=off_50");
      quick.push("ott+11_6_av=off:bs=on:cond=on:fsr=off:gs=on:gsem=off:irw=on:lma=on:nwc=10:sp=reverse_arity_100");
      quick.push("lrs+1010_4_aac=none:acc=model:add=large:afp=10000:afq=1.4:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=first:cond=on:fsr=off:irw=on:nwc=2:stl=30:sac=on:sp=reverse_arity:urr=ec_only_66");
      quick.push("lrs+1010_3:2_av=off:fsr=off:gs=on:gsem=off:irw=on:lwlo=on:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=ec_only_101");
      quick.push("dis+11_12_av=off:bsr=on:cond=on:lcm=predicate:lma=on:nwc=5:sp=reverse_arity:updr=off_33");
      quick.push("dis+1011_32_aac=none:afp=10000:afq=1.1:amm=sco:anc=none:cond=on:fsr=off:gs=on:gsem=on:lma=on:nwc=3:sas=z3:sp=reverse_arity_2");
      quick.push("dis+1011_3_av=off:nwc=1:sos=all:sp=reverse_arity_114");
      quick.push("lrs+1011_2:1_av=off:cond=on:lwlo=on:nwc=1.5:stl=30_187");
      quick.push("lrs+1011_2:1_afp=40000:afq=1.1:amm=off:anc=none:cond=on:ep=RST:fsr=off:gs=on:gsaa=full_model:gsem=on:nwc=1:sas=z3:stl=30:sos=all:sp=reverse_arity:updr=off:uhcvi=on_38");
      quick.push("dis+11_2:1_acc=model:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=first:er=known:gsp=on:irw=on:lma=on:nwc=5:sac=on:urr=ec_only_148");
      quick.push("lrs+4_1_av=off:bd=off:bsr=on:bce=on:fsr=off:irw=on:lcm=predicate:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on:uhcvi=on_39");
      quick.push("ott+1011_8:1_av=off:bd=off:cond=on:nwc=1:sos=all:sp=reverse_arity_182");
      quick.push("dis+1011_8_av=off:bd=off:cond=fast:er=known:fde=unused:gsp=on:lcm=predicate:lma=on:nwc=1.2:sp=reverse_arity:updr=off:uhcvi=on_33");
      quick.push("lrs+1011_2:1_av=off:cond=on:er=known:gs=on:gsem=on:lwlo=on:nwc=1.3:stl=30:updr=off:uhcvi=on_133");
      quick.push("lrs+1011_40_add=off:afp=1000:afq=2.0:anc=none:bs=unit_only:fsr=off:irw=on:nwc=1:sas=z3:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_68");
      quick.push("dis+2_10_afp=100000:afq=1.2:amm=sco:anc=none:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nwc=1_5");
      quick.push("lrs+4_4:1_add=large:afr=on:afp=100000:afq=1.0:anc=none:gs=on:gsem=off:irw=on:lcm=predicate:lma=on:lwlo=on:nwc=1.5:sas=z3:stl=30:sos=all:sac=on:sp=reverse_arity_148");
      quick.push("lrs+1011_10_av=off:bs=unit_only:bsr=on:er=filter:gsp=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nwc=1.2:stl=30:sp=reverse_arity:updr=off_105");
      quick.push("lrs+4_5_av=off:bd=off:bs=on:bsr=on:fsr=off:gs=on:gsem=off:nwc=2.5:stl=30:sp=occurrence:updr=off_139");
      quick.push("lrs+1011_5:1_afp=100000:afq=1.0:anc=none:bd=off:gsp=on:gs=on:gsem=off:lwlo=on:nwc=5:nicw=on:sas=z3:stl=30:sac=on:updr=off_176");
    }
    break;

  case Property::HEQ:
    quick.push("dis+10_6_av=off:cond=on:gs=on:lcm=reverse:lma=on:nwc=1.7:sp=reverse_arity:updr=off_7");
    quick.push("lrs+11_24_afp=100000:afq=1.0:amm=sco:anc=none:bd=off:bsr=on:irw=on:nwc=3:stl=30_3");
    quick.push("lrs+11_3:1_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=10:sas=z3:stl=30:updr=off_174");
    quick.push("lrs+11_4_aac=none:acc=model:add=large:afp=100000:afq=1.2:amm=off:anc=none:ccuc=first:cond=fast:gs=on:lma=on:nwc=4:stl=30:sac=on:sp=occurrence_237");
    quick.push("lrs+1011_20_acc=on:add=large:afr=on:afp=100000:afq=2.0:amm=sco:anc=none:bs=on:ccuc=small_ones:cond=on:gs=on:irw=on:lwlo=on:nwc=1:stl=30:sp=occurrence_37");
    quick.push("dis+10_4_aac=none:afp=10000:afq=2.0:amm=sco:anc=none:bd=off:cond=on:irw=on:lcm=reverse:lwlo=on:nwc=2.5:sas=z3:sp=reverse_arity_4");
    quick.push("lrs+10_40_aac=none:acc=on:add=off:afp=1000:afq=1.2:amm=sco:anc=none:bd=off:bsr=on:ccuc=first:cond=fast:fsr=off:fde=none:gs=on:gsem=on:lma=on:nwc=1.3:stl=30:sp=reverse_arity:updr=off:uhcvi=on_38");
    quick.push("ott+11_64_add=large:afp=1000:afq=2.0:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nwc=2_246");
    quick.push("lrs+2_14_aac=none:add=off:afp=100000:afq=1.1:anc=none:nwc=3:sas=z3:stl=30:sac=on:sp=reverse_arity:updr=off_167");
    quick.push("lrs+11_40_add=off:afp=10000:afq=1.2:amm=off:cond=on:fsr=off:lma=on:nwc=1.7:stl=30:sac=on:sp=occurrence_182");
    quick.push("lrs+11_3:2_add=off:afr=on:afp=4000:afq=1.4:anc=none:cond=on:lma=on:lwlo=on:nwc=3:sas=z3:stl=30:sac=on:sp=reverse_arity_124");
    quick.push("lrs+11_4:1_av=off:bce=on:cond=fast:fde=none:gsp=on:lma=on:nwc=5:stl=30:sp=occurrence_118");
    quick.push("dis+11_28_add=off:afr=on:afp=40000:afq=2.0:anc=none:cond=on:fsr=off:gs=on:gsem=on:lma=on:nwc=1:sas=z3:sp=reverse_arity:updr=off_53");
    quick.push("ott+11_2:1_afp=1000:afq=1.0:bd=preordered:fsr=off:fde=none:lma=on:nwc=1:sos=all:sp=occurrence:uhcvi=on_171");
    quick.push("lrs+10_3:1_add=off:afp=40000:afq=1.4:anc=none:br=off:fsr=off:gs=on:gsem=on:irw=on:lwlo=on:nwc=1:nicw=on:sas=z3:stl=30:sos=all:urr=on_222");
    quick.push("lrs+10_1024_av=off:bd=off:fsr=off:lma=on:nwc=1:stl=30:sp=occurrence:urr=on_205");
    break;

  case Property::PEQ:
    if (prop == 1) {
      quick.push("lrs+11_3:2_afp=10000:afq=1.0:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:irw=on:nwc=1.5:sas=z3:stl=30:sac=on:updr=off_7");
      quick.push("lrs+11_128_aac=none:add=large:afp=4000:afq=2.0:amm=sco:bd=off:gs=on:gsem=on:nwc=1:nicw=on:stl=30:sos=all:sac=on:sp=reverse_arity:updr=off_15");
      quick.push("lrs+11_6_aac=none:add=off:afp=100000:afq=1.1:amm=off:anc=none:bd=off:fsr=off:gs=on:gsem=off:nwc=1:sas=z3:stl=30:sp=occurrence_33");
      quick.push("dis+10_5_add=off:afr=on:afp=10000:afq=1.4:anc=none:er=known:gs=on:gsem=off:lma=on:nwc=1:nicw=on:sas=z3:sac=on:sp=reverse_arity_5");
      quick.push("lrs+1011_7_av=off:irw=on:nwc=1:stl=30:sos=all_69");
      quick.push("dis+1011_2:3_av=off:irw=on:nwc=1.2:sp=reverse_arity:updr=off_157");
      quick.push("lrs+11_2:3_add=large:afp=4000:afq=2.0:amm=sco:anc=none:er=known:gs=on:nwc=1:sas=z3:stl=30:updr=off_4");
      quick.push("lrs+10_5_av=off:bd=off:bs=unit_only:cond=on:fsr=off:gs=on:gsem=on:irw=on:lma=on:nwc=1:stl=30:sp=occurrence_223");
      quick.push("ott+11_1_afr=on:anc=none:cond=on:fsr=off:gs=on:gsem=on:lma=on:nwc=1:sac=on:sp=occurrence:updr=off:uhcvi=on_624");
      quick.push("lrs+11_32_add=off:afp=10000:afq=1.1:anc=all:bs=unit_only:cond=fast:fde=none:gs=on:gsaa=from_current:irw=on:lma=on:nwc=1:nicw=on:stl=60:sos=all:sac=on:sp=occurrence:updr=off:uhcvi=on_501");
      quick.push("lrs+11_2:1_av=off:cond=fast:fde=none:gs=on:gsem=off:lwlo=on:nwc=2:stl=60:sp=occurrence:updr=off:uhcvi=on_546");
    }
    else {
      quick.push("lrs+11_3:2_afp=10000:afq=1.0:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:irw=on:nwc=1.5:sas=z3:stl=30:sac=on:updr=off_7");
      quick.push("lrs+11_1024_add=off:afp=10000:afq=1.0:anc=none:bd=off:fsr=off:gs=on:gsem=on:irw=on:nwc=1.5:sas=z3:stl=30:sp=occurrence:updr=off_9");
      quick.push("lrs+11_5_acc=on:add=large:afr=on:afp=100000:afq=1.0:anc=none:bs=unit_only:ccuc=first:cond=on:lma=on:lwlo=on:nwc=1:stl=30:sp=reverse_arity:updr=off_234");
      quick.push("ott+1010_14_add=large:afp=40000:afq=1.1:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:lma=on:nwc=1.2:sp=occurrence:updr=off_259");
      quick.push("lrs+11_2:3_add=large:afp=4000:afq=2.0:amm=sco:anc=none:er=known:gs=on:nwc=1:sas=z3:stl=30:updr=off_1");
      quick.push("lrs+11_3:1_add=off:afr=on:afp=100000:afq=1.4:anc=none:cond=on:gs=on:irw=on:lma=on:lwlo=on:nwc=1:nicw=on:sas=z3:stl=30:sac=on:sp=occurrence:updr=off_298");
      quick.push("dis+10_28_add=large:afp=4000:afq=1.0:amm=sco:anc=none:bs=unit_only:cond=fast:fsr=off:gs=on:gsem=off:nwc=1:nicw=on:sas=z3:sos=all:sp=occurrence_72");
      quick.push("dis+1011_8_av=off:bsr=on:cond=on:fsr=off:fde=none:gs=on:lma=on:nwc=1.1:sos=all:sp=reverse_arity_207");
      quick.push("lrs+2_2_acc=model:add=off:afp=10000:afq=1.2:anc=all:bd=off:bs=on:bsr=on:ccuc=small_ones:cond=on:fsr=off:fde=unused:gs=on:lma=on:nwc=1.2:stl=30:sos=on:updr=off:uhcvi=on_43");
      quick.push("lrs+10_4:1_av=off:bd=off:bs=unit_only:bsr=on:fsr=off:gs=on:gsem=on:lwlo=on:nwc=1:stl=30:sos=all_135");
      quick.push("ott+1_3_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bsr=on:cond=fast:fsr=off:gs=on:gsem=on:nwc=1:nicw=on:sas=z3:sos=all:sp=occurrence:uhcvi=on_138");
      quick.push("ott+11_5:1_add=off:afp=10000:afq=1.4:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:lma=on:nwc=1_147");
      quick.push("lrs+10_5:4_add=large:afr=on:amm=sco:anc=all_dependent:bd=preordered:bs=unit_only:cond=on:fsr=off:gs=on:gsaa=from_current:gsem=on:lwlo=on:nwc=1:sas=z3:stl=60:sos=all:sac=on:updr=off:uhcvi=on_142");
      quick.push("ott+11_7_acc=model:afr=on:afp=40000:afq=2.0:amm=off:anc=all_dependent:bs=unit_only:ccuc=small_ones:fsr=off:gs=on:gsaa=from_current:lma=on:nwc=1.7:nicw=on:sp=occurrence:uhcvi=on_116");
      quick.push("lrs+11_2_add=large:afp=4000:afq=1.1:anc=none:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_110");
      quick.push("lrs+10_2_afr=on:afp=4000:afq=1.0:anc=none:cond=fast:fde=none:gs=on:gsem=off:lwlo=on:nwc=1:nicw=on:sas=z3:stl=30:sos=all:sac=on:sp=occurrence:updr=off_107");
      quick.push("ott+1011_5_afr=on:afp=1000:afq=1.4:amm=sco:bs=unit_only:bsr=on:cond=fast:fde=unused:gsp=on:gs=on:nwc=1:nicw=on:sas=z3:sos=all:updr=off:uhcvi=on_484");
      quick.push("lrs+11_3_aac=none:add=large:afp=1000:afq=1.4:anc=all_dependent:bd=off:bs=on:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=1:stl=60:sos=all:sac=on:sp=occurrence:updr=off_587");
    }
    break;

  case Property::HNE:
    quick.push("lrs+1011_8_add=large:afr=on:afp=40000:afq=1.2:amm=off:anc=none:bs=on:gs=on:gsem=off:nwc=1.5:nicw=on:stl=30:sac=on:sp=reverse_arity:updr=off_32");
    quick.push("dis+11_1_add=off:afp=4000:afq=2.0:amm=sco:anc=none:br=off:cond=on:lma=on:nwc=1:sos=all:sac=on:urr=on_7");
    quick.push("lrs+10_2:3_av=off:bsr=on:cond=on:lwlo=on:nwc=1.7:stl=60:sp=occurrence:updr=off_171");
    quick.push("dis+1_40_av=off:lwlo=on:nwc=4:sos=all:sp=occurrence:updr=off_117");
    quick.push("lrs+4_3_add=off:afr=on:afp=10000:afq=2.0:anc=none:lma=on:nwc=1.1:nicw=on:sas=z3:stl=30:sac=on_203");
    quick.push("lrs+10_3:2_afr=on:afp=100000:afq=2.0:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:lwlo=on:nwc=2:nicw=on:stl=30:sp=reverse_arity_211");
    quick.push("lrs+10_2:3_av=off:cond=on:fsr=off:lwlo=on:nwc=2.5:stl=30:sp=reverse_arity:updr=off_68");
    quick.push("lrs+1011_3_av=off:bs=unit_only:cond=on:fsr=off:lcm=predicate:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence_215");
    quick.push("lrs+11_24_afp=4000:afq=2.0:amm=sco:anc=all:br=off:cond=fast:gsp=on:gs=on:gsem=on:lma=on:lwlo=on:nwc=1.7:nicw=on:stl=30:sos=theory:sac=on:sp=reverse_arity:urr=on_122");
    quick.push("lrs+10_5:4_av=off:bsr=on:gs=on:gsem=off:lma=on:nwc=4:stl=30:uhcvi=on_146");
    quick.push("lrs+1_128_afp=100000:afq=2.0:anc=none:cond=fast:fsr=off:gs=on:gsem=on:lma=on:nwc=1:sas=z3:stl=60:sac=on_455");
    quick.push("dis+11_3:1_aac=none:add=off:afp=4000:afq=1.4:fsr=off:nwc=3:nicw=on:sp=occurrence_101");
    quick.push("dis+11_8:1_afr=on:afp=1000:afq=1.0:amm=off:anc=none:nwc=1:sos=all:sp=occurrence:updr=off_184");
    quick.push("lrs+1_2:3_av=off:fsr=off:lma=on:nwc=1:sas=z3:stl=30:urr=ec_only:updr=off_72");
    break;

  case Property::NNE:
    quick.push("dis+1011_5_av=off:gs=on:gsem=on:nwc=1:sos=on:updr=off_3");
    quick.push("dis+1011_64_add=large:afr=on:afp=40000:afq=1.2:amm=off:anc=none:gsp=on:gs=on:gsem=on:lma=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off:uhcvi=on_26");
    quick.push("lrs+11_14_aac=none:afp=1000:afq=2.0:fsr=off:lma=on:nwc=1:stl=30:sp=reverse_arity_26");
    quick.push("dis-1_3_av=off:cond=on:fsr=off:gs=on:gsem=on:nwc=1:updr=off_4");
    quick.push("dis+10_5:4_afp=100000:afq=1.0:amm=sco:anc=all:cond=fast:fsr=off:gs=on:lma=on:nwc=1:sp=reverse_arity:updr=off:uhcvi=on_24");
    quick.push("dis+1011_5_av=off:lma=on:nwc=1.7:sos=all:sp=reverse_arity:updr=off_430");
    quick.push("lrs+1011_50_av=off:bs=unit_only:cond=on:nwc=2:stl=30:sp=occurrence:updr=off_47");
    quick.push("dis+4_7_av=off:cond=fast:gsp=on:lma=on:nwc=1.3:sp=occurrence:urr=ec_only:uhcvi=on_162");
    quick.push("dis+3_64_av=off:cond=fast:lcm=reverse:lma=on:lwlo=on:nwc=1:sos=on:updr=off_68");
    quick.push("lrs+1011_2_av=off:cond=on:gsp=on:gs=on:lwlo=on:nwc=1:stl=30:sos=all:uhcvi=on_300");
    quick.push("lrs+4_20_av=off:gs=on:gsem=off:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:updr=off_43");
    quick.push("lrs+1010_14_av=off:fsr=off:lma=on:lwlo=on:nwc=2.5:stl=30:updr=off:uhcvi=on_82");
    quick.push("lrs+1011_3:2_av=off:bs=on:cond=on:gsp=on:gs=on:gsem=off:lcm=predicate:lwlo=on:nwc=2.5:stl=30:sos=all:updr=off_158");
    quick.push("dis+2_2_add=off:afr=on:afp=4000:afq=1.0:amm=sco:anc=none:fsr=off:lcm=predicate:lma=on:nwc=1.3:nicw=on:sos=theory:sp=reverse_arity:urr=ec_only:updr=off_26");
    quick.push("dis+1003_128_add=large:afr=on:amm=off:cond=fast:fsr=off:gs=on:gsem=on:nwc=1:sas=z3:sos=on:sp=occurrence:updr=off:uhcvi=on_64");
    quick.push("lrs+11_2_afp=1000:afq=1.4:amm=sco:anc=none:cond=on:gs=on:gsem=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_155");
    break;

  case Property::UEQ:
    if (prop == 4096) {
      quick.push("lrs+10_4:1_av=off:bd=preordered:fde=none:ins=3:lwlo=on:nwc=3:stl=60:sp=reverse_arity_113");
      quick.push("ott+10_128_av=off:bd=off:ins=3:nwc=1:sp=reverse_arity_45");
      quick.push("ott+10_4_av=off:bd=off:ins=3:nwc=1.5:sp=reverse_arity_568");
      quick.push("ott+10_8_awrs=converge:awrsf=8:av=off:bd=preordered:ins=3:nwc=1:s2a=on_1858");
    }
    else if (prop == 0) {
      if (atoms > 12) {
        quick.push("ott+10_16_av=off:ins=3:nwc=1.2_1139");
        quick.push("lrs+10_3:1_awrs=decay:awrsf=512:av=off:fde=unused:ins=3:nwc=1:stl=150:s2a=on:sp=frequency:uhcvi=on_103");
        quick.push("ott+10_12_awrs=decay:awrsf=32:av=off:bd=preordered:ins=3:nwc=1:s2a=on:sp=frequency:uhcvi=on_107");
        quick.push("lrs+10_14_awrs=decay:awrsf=128:av=off:bd=off:fde=none:ins=3:nwc=1:stl=60:s2a=on_208");
        quick.push("ott+10_28_av=off:bd=preordered:ins=3:nwc=3:sp=reverse_arity_966");
      }
      else if (atoms > 10) {
        quick.push("lrs+10_3_av=off:fde=none:ins=3:lwlo=on:nwc=1.1:stl=60:sp=frequency_93");
        quick.push("ott+10_4_awrs=decay:awrsf=4:av=off:ins=3:nwc=1.2:sp=weighted_frequency:uhcvi=on_709");
        quick.push("ott+10_1024_awrs=converge:awrsf=512:av=off:bd=off:fde=none:ins=3:nwc=4_1341");
        quick.push("ott+10_6_av=off:bd=preordered:fde=none:ins=3:nwc=1.1:sos=on:sp=occurrence_786");
        quick.push("ott+10_12_awrs=decay:awrsf=16:av=off:bd=preordered:ins=3:nwc=1.2:sp=frequency_1980");
      }
      else {
        quick.push("ott+10_10_av=off:bd=preordered:fde=unused:ins=3:nwc=1.5_37");
        quick.push("lrs+10_1024_awrs=converge:awrsf=256:av=off:fde=unused:ins=3:lwlo=on:nwc=1.3:stl=90:sp=weighted_frequency:uhcvi=on_643");
        quick.push("lrs+10_3:1_av=off:bd=preordered:fde=unused:ins=3:lwlo=on:nwc=1:stl=150:sp=weighted_frequency_597");
        quick.push("lrs+10_4_awrs=decay:awrsf=512:av=off:bd=preordered:fde=unused:ins=3:nwc=2:stl=120:sp=frequency:uhcvi=on_1");
      }
    }
    else if (prop == 2) {
      if (atoms < 15) {
        quick.push("lrs+10_28_av=off:ins=3:nwc=1:stl=30_188");
        quick.push("ott+10_5:1_av=off:bd=preordered:fde=unused:ins=3:nwc=1_268");
        quick.push("ott+10_40_av=off:bd=preordered:fde=none:ins=3:nwc=1.2:sp=weighted_frequency:uhcvi=on_975");
        quick.push("ott+10_32_av=off:ins=3:nwc=1:sp=reverse_arity_171");
        quick.push("lrs+10_2:1_av=off:bd=off:fde=none:ins=3:lwlo=on:nwc=1:stl=90:uhcvi=on_292");
      }
      else if (atoms < 18) {
        quick.push("lrs+10_7_av=off:ins=3:lwlo=on:nwc=1.1:stl=150_80");
        quick.push("lrs+10_3_awrs=decay:awrsf=32:av=off:bd=preordered:ins=3:lwlo=on:nwc=1.2:stl=30:sp=reverse_arity_203");
        quick.push("ott+10_28_av=off:bd=preordered:fde=unused:ins=3:nwc=2.5:sp=occurrence_275");
        quick.push("ott+10_4_av=off:fde=none:ins=3:nwc=1:sos=on:sp=occurrence:uhcvi=on_122");
        quick.push("ott+10_8_av=off:bd=preordered:ins=3:nwc=1.2:sp=reverse_arity:uhcvi=on_456");
        quick.push("lrs+10_4:1_awrs=converge:awrsf=1:av=off:bd=preordered:ins=3:lwlo=on:nwc=1.3:stl=120:s2a=on:sp=weighted_frequency:uhcvi=on_363");
        quick.push("ott+10_2_av=off:bd=off:ins=3:nwc=1.2_430");
        quick.push("ott+10_4_av=off:bd=off:ins=3:nwc=1.5:sp=reverse_arity_1");
      }
      else {
        quick.push("ott+10_20_av=off:ins=3:nwc=1.5:sp=reverse_arity:uhcvi=on_862");
        quick.push("ott+10_12_awrs=converge:awrsf=64:av=off:bd=preordered:fde=unused:ins=3:nwc=1.5:sp=frequency:uhcvi=on_2028");
        quick.push("lrs+10_3:2_av=off:bd=preordered:ins=3:lwlo=on:nwc=1.1:stl=90:uhcvi=on_529");
      }
    }
    else {
      quick.push("lrs+10_5:1_av=off:bd=off:ins=3:nwc=2.5:stl=60:sp=reverse_arity_138");
      quick.push("lrs+10_128_awrs=converge:awrsf=16:av=off:bd=off:fde=unused:ins=3:lwlo=on:nwc=5:stl=120:s2a=on:sp=frequency_349");
      quick.push("ott+10_28_av=off:bd=preordered:fde=unused:ins=3:nwc=2.5:sp=occurrence_36");
      quick.push("lrs+1011_8_av=off:bs=unit_only:ep=RSTC:gsp=on:gs=on:gsem=on:lwlo=on:nwc=1:stl=30_226");
    }
    break;
  }

  switch (cat) {
  case Property::HEQ:
  case Property::PEQ:
  case Property::NEQ:
  case Property::HNE:
  case Property::NNE:
    fallback.push("lrs+1011_5:1_afp=100000:afq=1.0:anc=none:bd=off:gsp=on:gs=on:gsem=off:lwlo=on:nwc=5:nicw=on:sas=z3:sac=on:updr=off_300");
    fallback.push("lrs+10_2:3_av=off:bsr=on:cond=on:lwlo=on:nwc=1.7:sp=occurrence:updr=off_600");
    fallback.push("dis+1011_5_av=off:lma=on:nwc=1.7:sos=all:sp=reverse_arity:updr=off_600");
    fallback.push("lrs+11_3:1_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=10:sas=z3:updr=off_300");
    fallback.push("lrs+11_2_add=large:afp=4000:afq=1.1:anc=none:lma=on:lwlo=on:nwc=1:sp=occurrence:updr=off_300");
    fallback.push("lrs+4_2_av=off:bs=on:er=known:gs=on:irw=on:lwlo=on:nwc=10:sp=occurrence_300");
    fallback.push("dis+1011_3_av=off:nwc=1:sos=all:sp=reverse_arity_300");
    fallback.push("lrs+1011_3:1_add=large:afr=on:afp=40000:afq=1.2:amm=off:anc=none:bce=on:fde=unused:gs=on:gsem=off:irw=on:lwlo=on:nwc=1:sd=3:ss=axioms:st=3.0:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_300");
    fallback.push("lrs+11_2_afr=on:afp=100000:afq=1.4:amm=off:gsp=on:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on:updr=off_300");
    fallback.push("lrs+1011_3_av=off:bs=unit_only:cond=on:fsr=off:lcm=predicate:lma=on:lwlo=on:nwc=1:sp=occurrence_300");
    fallback.push("lrs+1011_2:1_av=off:cond=on:er=known:gs=on:gsem=on:lwlo=on:nwc=1.3:updr=off:uhcvi=on_300");
    fallback.push("ott+11_14_av=off:cond=on:nwc=1.3:sp=reverse_arity:updr=off_300");
    fallback.push("lrs+11_4_aac=none:acc=model:add=large:afp=100000:afq=1.2:amm=off:anc=none:ccuc=first:cond=fast:gs=on:lma=on:nwc=4:sac=on:sp=occurrence_300");
    fallback.push("dis+2_2_add=off:afr=on:afp=4000:afq=1.0:amm=sco:anc=none:fsr=off:lcm=predicate:lma=on:nwc=1.3:nicw=on:sos=theory:sp=reverse_arity:urr=ec_only:updr=off_300");
    fallback.push("dis+10_1_add=off:afp=4000:afq=1.4:amm=off:anc=none:cond=on:irw=on:nwc=1:sas=z3:sd=1:ss=axioms:st=3.0:sos=all:sp=occurrence_300");
    fallback.push("lrs+11_5_add=large:afr=on:afp=40000:afq=1.2:cond=on:er=known:gs=on:gsem=off:nwc=1.5:sp=occurrence:updr=off_300");
    fallback.push("lrs+1003_3_av=off:bd=off:fde=none:gs=on:lma=on:nwc=1:sd=7:ss=axioms:st=1.2:sos=all:sp=reverse_arity:updr=off:uhcvi=on_300");
    fallback.push("lrs-1_14_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:cond=on:gs=on:gsem=off:nwc=1:nicw=on:sas=z3:sd=1:ss=axioms:sp=reverse_arity:urr=ec_only:updr=off_300");
    fallback.push("lrs+11_6_afr=on:afp=100000:afq=1.1:anc=none:br=off:gs=on:lma=on:nwc=3:sac=on:sp=occurrence:urr=on:updr=off_300");
    fallback.push("lrs+4_4:1_add=large:afr=on:afp=100000:afq=1.0:anc=none:gs=on:gsem=off:irw=on:lcm=predicate:lma=on:lwlo=on:nwc=1.5:sas=z3:sos=all:sac=on:sp=reverse_arity_300");
    fallback.push("lrs+11_3_aac=none:add=large:afp=1000:afq=1.4:anc=all_dependent:bd=off:bs=on:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=1:sos=all:sac=on:sp=occurrence:updr=off_600");
    fallback.push("ott+11_64_add=large:afp=1000:afq=2.0:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nwc=2_300");
    fallback.push("lrs+1011_3:2_av=off:bs=on:cond=on:gsp=on:gs=on:gsem=off:lcm=predicate:lwlo=on:nwc=2.5:sos=all:updr=off_300");
    fallback.push("lrs+10_3_av=off:bd=off:cond=on:gs=on:gsem=off:irw=on:lwlo=on:nwc=1.2:sp=reverse_arity:updr=off_300");
    fallback.push("lrs-11_10_afr=on:afp=1000:afq=1.0:amm=off:anc=none:gs=on:irw=on:lma=on:nwc=2.5:sac=on:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("lrs+1010_4_aac=none:acc=model:add=large:afp=10000:afq=1.4:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=first:cond=on:fsr=off:irw=on:nwc=2:sac=on:sp=reverse_arity:urr=ec_only_300");
    fallback.push("dis+10_28_add=large:afp=4000:afq=1.0:amm=sco:anc=none:bs=unit_only:cond=fast:fsr=off:gs=on:gsem=off:nwc=1:nicw=on:sas=z3:sos=all:sp=occurrence_300");
    fallback.push("lrs+4_1_av=off:bd=off:bsr=on:bce=on:fsr=off:irw=on:lcm=predicate:nwc=1:sos=all:sp=reverse_arity:urr=on:uhcvi=on_300");
    fallback.push("dis+10_4_aac=none:afp=10000:afq=2.0:amm=sco:anc=none:bd=off:cond=on:irw=on:lcm=reverse:lwlo=on:nwc=2.5:sas=z3:sp=reverse_arity_300");
    fallback.push("lrs+11_5_acc=on:add=large:afr=on:afp=100000:afq=1.0:anc=none:bs=unit_only:ccuc=first:cond=on:lma=on:lwlo=on:nwc=1:sp=reverse_arity:updr=off_300");
    fallback.push("dis+1_40_av=off:lwlo=on:nwc=4:sos=all:sp=occurrence:updr=off_300");
    fallback.push("dis+10_5_add=off:afr=on:afp=10000:afq=1.4:anc=none:er=known:gs=on:gsem=off:lma=on:nwc=1:nicw=on:sas=z3:sac=on:sp=reverse_arity_300");
    fallback.push("lrs+4_5_av=off:bd=off:bs=on:bsr=on:fsr=off:gs=on:gsem=off:nwc=2.5:sp=occurrence:updr=off_300");
    fallback.push("dis+2_3_av=off:cond=on:fsr=off:lcm=reverse:lma=on:nwc=1:sos=on:sp=reverse_arity_300");
    fallback.push("dis+1011_2:1_av=off:lma=on:nwc=1:sd=3:ss=axioms:st=5.0:sp=occurrence:urr=ec_only_300");
    fallback.push("dis+1011_8_av=off:bd=off:cond=fast:er=known:fde=unused:gsp=on:lcm=predicate:lma=on:nwc=1.2:sp=reverse_arity:updr=off:uhcvi=on_300");
    fallback.push("lrs+1011_4:1_av=off:cond=on:irw=on:lma=on:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_300");
    fallback.push("ott+1011_2:3_av=off:cond=fast:er=filter:fde=unused:gsp=on:irw=on:nwc=3:sp=occurrence:updr=off:uhcvi=on_300");
    fallback.push("lrs+10_3:2_afr=on:afp=100000:afq=2.0:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:lwlo=on:nwc=2:nicw=on:sp=reverse_arity_300");
    fallback.push("dis+11_2:1_acc=model:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=first:er=known:gsp=on:irw=on:lma=on:nwc=5:sac=on:urr=ec_only_300");
    fallback.push("lrs+11_40_add=off:afp=10000:afq=1.2:amm=off:cond=on:fsr=off:lma=on:nwc=1.7:sac=on:sp=occurrence_300");
    fallback.push("lrs+10_5:4_av=off:bsr=on:gs=on:gsem=off:lma=on:nwc=4:uhcvi=on_300");
    fallback.push("lrs+1010_3:1_av=off:cond=on:nwc=5:sp=reverse_arity_300");
    fallback.push("lrs+11_3:2_add=off:afr=on:afp=4000:afq=1.4:anc=none:cond=on:lma=on:lwlo=on:nwc=3:sas=z3:sac=on:sp=reverse_arity_300");
    fallback.push("lrs+4_3_add=off:afr=on:afp=10000:afq=2.0:anc=none:lma=on:nwc=1.1:nicw=on:sas=z3:sac=on_300");
    fallback.push("ott+11_6_av=off:bs=on:cond=on:fsr=off:gs=on:gsem=off:irw=on:lma=on:nwc=10:sp=reverse_arity_300");
    fallback.push("dis+11_12_av=off:bsr=on:cond=on:lcm=predicate:lma=on:nwc=5:sp=reverse_arity:updr=off_300");
    fallback.push("lrs+11_3:1_add=off:afr=on:afp=100000:afq=1.4:anc=none:cond=on:gs=on:irw=on:lma=on:lwlo=on:nwc=1:nicw=on:sas=z3:sac=on:sp=occurrence:updr=off_300");
    fallback.push("lrs+11_1_av=off:bsr=on:fde=none:irw=on:lma=on:lwlo=on:nwc=1:sp=occurrence_300");
    fallback.push("ott+1011_5_afr=on:afp=1000:afq=1.4:amm=sco:bs=unit_only:bsr=on:cond=fast:fde=unused:gsp=on:gs=on:nwc=1:nicw=on:sas=z3:sos=all:updr=off:uhcvi=on_600");
    fallback.push("ott+1010_14_add=large:afp=40000:afq=1.1:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:lma=on:nwc=1.2:sp=occurrence:updr=off_300");
    fallback.push("lrs+11_2_afp=1000:afq=1.4:amm=sco:anc=none:cond=on:gs=on:gsem=on:lcm=reverse:lma=on:nwc=1:sos=all:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("lrs+11_3:2_afp=10000:afq=1.0:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:irw=on:nwc=1.5:sas=z3:sac=on:updr=off_300");
    fallback.push("lrs+1011_40_add=off:afp=1000:afq=2.0:anc=none:bs=unit_only:fsr=off:irw=on:nwc=1:sas=z3:sos=on:sac=on:sp=reverse_arity:updr=off_300");
    fallback.push("dis+1011_12_av=off:bd=off:bs=unit_only:fsr=off:lma=on:nwc=1:urr=ec_only:updr=off_300");
    fallback.push("lrs+1011_7_av=off:irw=on:nwc=1:sos=all_300");
    fallback.push("lrs+10_12_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=off:cond=on:er=filter:lcm=predicate:lma=on:lwlo=on:nwc=1.3:sas=z3:sac=on_300");
    fallback.push("lrs+1_3_av=off:fsr=off:lma=on:nwc=1:sd=1:ss=axioms:sp=occurrence:urr=on_300");
    fallback.push("dis+11_5_afr=on:afp=100000:afq=1.2:amm=sco:anc=none:cond=on:fsr=off:gs=on:gsem=off:irw=on:lma=on:nwc=1.7:sas=z3:sac=on:sp=reverse_arity:urr=ec_only:updr=off_300");
    fallback.push("lrs+1011_2:1_av=off:bce=on:cond=fast:fsr=off:fde=none:lwlo=on:nwc=1:sd=1:ss=axioms:st=3.0:sp=occurrence:urr=ec_only:updr=off_300");
    fallback.push("dis+4_7_av=off:cond=fast:gsp=on:lma=on:nwc=1.3:sp=occurrence:urr=ec_only:uhcvi=on_300");
    fallback.push("lrs+1011_50_av=off:bs=unit_only:cond=on:nwc=2:sp=occurrence:updr=off_300");
    fallback.push("lrs+1011_3:1_av=off:bs=unit_only:bsr=on:er=known:fsr=off:fde=unused:irw=on:lcm=reverse:lwlo=on:nwc=1.7:sos=on:sp=occurrence:updr=off_300");
    fallback.push("lrs+10_1024_av=off:bd=off:fsr=off:lma=on:nwc=1:sp=occurrence:urr=on_300");
    fallback.push("lrs+10_3:1_add=off:afp=40000:afq=1.4:anc=none:br=off:fsr=off:gs=on:gsem=on:irw=on:lwlo=on:nwc=1:nicw=on:sas=z3:sos=all:urr=on_300");
    fallback.push("lrs+1_128_afp=100000:afq=2.0:anc=none:cond=fast:fsr=off:gs=on:gsem=on:lma=on:nwc=1:sas=z3:sac=on_600");
    fallback.push("lrs+1010_3:2_av=off:fsr=off:gs=on:gsem=off:irw=on:lwlo=on:nwc=1:sos=all:sp=reverse_arity:urr=ec_only_300");
    fallback.push("lrs+1011_20_acc=on:add=large:afr=on:afp=100000:afq=2.0:amm=sco:anc=none:bs=on:ccuc=small_ones:cond=on:gs=on:irw=on:lwlo=on:nwc=1:sp=occurrence_300");
    fallback.push("lrs+1010_14_av=off:fsr=off:lma=on:lwlo=on:nwc=2.5:updr=off:uhcvi=on_300");
    fallback.push("lrs+1011_2:1_add=large:afr=on:afp=100000:afq=2.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:lma=on:nwc=1:sd=7:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on_300");
    fallback.push("ott+10_4:1_av=off:bd=preordered:cond=fast:fde=unused:irw=on:lcm=reverse:nwc=3:sd=2:ss=axioms:st=5.0:sp=reverse_arity:uhcvi=on_300");
    fallback.push("lrs+2_14_aac=none:add=off:afp=100000:afq=1.1:anc=none:nwc=3:sas=z3:sac=on:sp=reverse_arity:updr=off_300");
    fallback.push("lrs+10_5:4_add=large:afr=on:amm=sco:anc=all_dependent:bd=preordered:bs=unit_only:cond=on:fsr=off:gs=on:gsaa=from_current:gsem=on:lwlo=on:nwc=1:sas=z3:sos=all:sac=on:updr=off:uhcvi=on_600");
    fallback.push("ott+1011_8:1_av=off:bd=off:cond=on:nwc=1:sos=all:sp=reverse_arity_300");
    fallback.push("dis+11_28_add=off:afr=on:afp=40000:afq=2.0:anc=none:cond=on:fsr=off:gs=on:gsem=on:lma=on:nwc=1:sas=z3:sp=reverse_arity:updr=off_300");
    fallback.push("lrs+1_20_add=large:afr=on:afp=4000:afq=1.2:amm=off:anc=none:cond=on:fsr=off:gs=on:gsem=off:lwlo=on:nwc=1:sas=z3:sd=3:ss=axioms:st=1.2:sp=occurrence:updr=off_300");
    fallback.push("lrs+11_14_av=off:bd=off:bs=unit_only:cond=on:gsp=on:gs=on:gsem=on:irw=on:lcm=reverse:lwlo=on:nwc=1:sos=on:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("dis+3_64_av=off:cond=fast:lcm=reverse:lma=on:lwlo=on:nwc=1:sos=on:updr=off_300");
    fallback.push("dis+1011_5_av=off:gs=on:gsem=on:nwc=1:sos=on:updr=off_300");
    fallback.push("dis+1003_128_add=large:afr=on:amm=off:cond=fast:fsr=off:gs=on:gsem=on:nwc=1:sas=z3:sos=on:sp=occurrence:updr=off:uhcvi=on_300");
    fallback.push("dis-11_4:1_amm=sco:anc=none:cond=on:fsr=off:gsp=on:lma=on:nwc=10:sac=on:sp=reverse_arity:urr=on_300");
    fallback.push("lrs+11_1_av=off:fsr=off:irw=on:lma=on:lwlo=on:nwc=1:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("dis+2_10_afp=100000:afq=1.2:amm=sco:anc=none:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nwc=1_300");
    fallback.push("lrs+10_2:3_av=off:cond=on:fsr=off:lwlo=on:nwc=2.5:sp=reverse_arity:updr=off_300");
    fallback.push("dis+1010_1024_afr=on:afp=10000:afq=2.0:amm=off:anc=none:fsr=off:gs=on:irw=on:lwlo=on:nwc=1:sas=z3:sd=1:ss=axioms:st=3.0_300");
    fallback.push("lrs+1002_3:1_av=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nwc=4:sas=z3:sd=1:ss=axioms:st=5.0:sp=reverse_arity_300");
    fallback.push("lrs+10_5:1_add=large:afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=off:lcm=predicate:nwc=1:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_300");
    fallback.push("lrs+1011_5:4_av=off:bd=off:fsr=off:gs=on:nwc=1.3:urr=ec_only:updr=off_300");
    fallback.push("lrs+10_40_aac=none:acc=on:add=off:afp=1000:afq=1.2:amm=sco:anc=none:bd=off:bsr=on:ccuc=first:cond=fast:fsr=off:fde=none:gs=on:gsem=on:lma=on:nwc=1.3:sp=reverse_arity:updr=off:uhcvi=on_300");
    fallback.push("dis+1011_32_aac=none:afp=10000:afq=1.1:amm=sco:anc=none:cond=on:fsr=off:gs=on:gsem=on:lma=on:nwc=3:sas=z3:sp=reverse_arity_300");
    fallback.push("dis+1011_64_add=large:afr=on:afp=40000:afq=1.2:amm=off:anc=none:gsp=on:gs=on:gsem=on:lma=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off:uhcvi=on_300");
    fallback.push("lrs+1_32_av=off:bd=off:br=off:gs=on:gsem=on:irw=on:nwc=1:sd=1:ss=axioms:sp=occurrence:urr=on:updr=off_300");
    fallback.push("dis+11_3_av=off:bd=off:bsr=on:bce=on:gsp=on:gs=on:gsem=on:lma=on:nwc=2.5:sp=reverse_arity:urr=ec_only:uhcvi=on_300");
    fallback.push("lrs+11_24_afp=100000:afq=1.0:amm=sco:anc=none:bd=off:bsr=on:irw=on:nwc=3_300");
    fallback.push("lrs+1011_2:1_afp=40000:afq=1.1:amm=off:anc=none:cond=on:ep=RST:fsr=off:gs=on:gsaa=full_model:gsem=on:nwc=1:sas=z3:sos=all:sp=reverse_arity:updr=off:uhcvi=on_300");
    fallback.push("lrs+1010_8:1_av=off:bs=unit_only:br=off:cond=on:fsr=off:irw=on:nwc=1.3:sd=3:ss=axioms:st=3.0:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("lrs+1011_2_av=off:bs=unit_only:bsr=on:gs=on:gsem=on:nwc=3:updr=off_300");
    fallback.push("lrs+10_2_afr=on:afp=4000:afq=1.0:anc=none:cond=fast:fde=none:gs=on:gsem=off:lwlo=on:nwc=1:nicw=on:sas=z3:sos=all:sac=on:sp=occurrence:updr=off_300");
    fallback.push("dis-11_5:1_acc=model:add=off:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=first:cond=on:gs=on:gsem=off:nwc=1:sd=3:ss=axioms:st=1.2:sos=all_300");
    fallback.push("lrs+10_4:1_av=off:bd=off:bs=unit_only:bsr=on:fsr=off:gs=on:gsem=on:lwlo=on:nwc=1:sos=all_300");
    fallback.push("dis+2_5:4_add=large:afp=4000:afq=1.2:anc=all:bce=on:cond=fast:fde=none:lma=on:nwc=10:sd=1:ss=axioms:st=1.5:sac=on_300");
    fallback.push("lrs+10_5_av=off:bd=off:bs=unit_only:cond=on:fsr=off:gs=on:gsem=on:irw=on:lma=on:nwc=1:sp=occurrence_300");
    fallback.push("dis+1011_2:3_av=off:irw=on:nwc=1.2:sp=reverse_arity:updr=off_300");
    fallback.push("dis+1002_5:1_av=off:cond=fast:fsr=off:fde=none:lma=on:nwc=1:sd=3:ss=axioms:st=1.5:sos=all:urr=on:updr=off_300");
    fallback.push("lrs+2_2_acc=model:add=off:afp=10000:afq=1.2:anc=all:bd=off:bs=on:bsr=on:ccuc=small_ones:cond=on:fsr=off:fde=unused:gs=on:lma=on:nwc=1.2:sos=on:updr=off:uhcvi=on_300");
    fallback.push("dis+1003_3_add=off:afp=100000:afq=2.0:amm=sco:anc=none:bs=on:bsr=on:bce=on:cond=fast:fde=none:gs=on:gsaa=from_current:gsem=off:nwc=1.2:sas=z3:sac=on:sp=reverse_arity_300");
    fallback.push("dis+11_3:1_aac=none:add=off:afp=4000:afq=1.4:fsr=off:nwc=3:nicw=on:sp=occurrence_300");
    fallback.push("lrs+1011_2:1_av=off:cond=on:lwlo=on:nwc=1.5_300");
    fallback.push("lrs+11_24_afp=4000:afq=2.0:amm=sco:anc=all:br=off:cond=fast:gsp=on:gs=on:gsem=on:lma=on:lwlo=on:nwc=1.7:nicw=on:sos=theory:sac=on:sp=reverse_arity:urr=on_300");
    fallback.push("dis+10_5:4_afp=100000:afq=1.0:amm=sco:anc=all:cond=fast:fsr=off:gs=on:lma=on:nwc=1:sp=reverse_arity:updr=off:uhcvi=on_300");
    fallback.push("lrs-2_2:1_afr=on:afp=1000:afq=2.0:anc=none:bd=off:bce=on:cond=fast:gs=on:gsaa=from_current:gsem=on:lwlo=on:nwc=1.5:sac=on:sp=reverse_arity:uhcvi=on_300");
    fallback.push("lrs+1_2:1_av=off:fsr=off:lma=on:nwc=1:sd=7:ss=axioms:st=1.2:sos=on:urr=ec_only_300");
    fallback.push("dis+11_4_aac=none:add=large:afp=100000:afq=1.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:lcm=reverse:lma=on:nwc=1:sos=all:sac=on:sp=reverse_arity:urr=ec_only_300");
    fallback.push("lrs+1011_10_av=off:bs=unit_only:bsr=on:er=filter:gsp=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nwc=1.2:sp=reverse_arity:updr=off_300");
    fallback.push("dis-1_3_av=off:cond=on:fsr=off:gs=on:gsem=on:nwc=1:updr=off_300");
    fallback.push("lrs+11_4:1_av=off:bce=on:cond=fast:fde=none:gsp=on:lma=on:nwc=5:sp=occurrence_300");
    fallback.push("ott+11_7_acc=model:afr=on:afp=40000:afq=2.0:amm=off:anc=all_dependent:bs=unit_only:ccuc=small_ones:fsr=off:gs=on:gsaa=from_current:lma=on:nwc=1.7:nicw=on:sp=occurrence:uhcvi=on_300");
    fallback.push("ott+10_28_acc=model:add=off:afp=40000:afq=2.0:amm=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=on:fsr=off:gs=on:gsem=on:nwc=1.1:nicw=on:urr=on:updr=off_300");
    fallback.push("lrs+1011_2_av=off:bd=preordered:bs=unit_only:cond=fast:fsr=off:fde=unused:irw=on:lma=on:lwlo=on:nwc=1.2:sp=occurrence:uhcvi=on_300");
    fallback.push("dis+11_8:1_afr=on:afp=1000:afq=1.0:amm=off:anc=none:nwc=1:sos=all:sp=occurrence:updr=off_300");
    fallback.push("dis+10_3_acc=on:afr=on:afp=1000:afq=1.0:amm=sco:bs=unit_only:ccuc=first:fsr=off:irw=on:lcm=reverse:lma=on:nwc=1.5:updr=off_300");
    fallback.push("ott+11_5:1_add=off:afp=10000:afq=1.4:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:lma=on:nwc=1_300");
    fallback.push("lrs+1004_20_av=off:cond=on:er=filter:gsp=on:gs=on:gsem=on:lcm=reverse:nwc=1:sd=3:ss=axioms:st=3.0:sos=on:urr=ec_only_300");
    fallback.push("dis+1011_8_av=off:bsr=on:cond=on:fsr=off:fde=none:gs=on:lma=on:nwc=1.1:sos=all:sp=reverse_arity_300");
    fallback.push("lrs+11_14_aac=none:afp=1000:afq=2.0:fsr=off:lma=on:nwc=1:sp=reverse_arity_300");
    fallback.push("dis+11_3_add=off:afr=on:afp=4000:afq=2.0:amm=off:anc=none:cond=on:gs=on:gsem=off:irw=on:lma=on:lwlo=on:nwc=1:sas=z3:sos=on:sac=on:updr=off_300");
    fallback.push("lrs+1_2:3_av=off:fsr=off:lma=on:nwc=1:sas=z3:urr=ec_only:updr=off_300");
    fallback.push("ott+11_2:1_afp=1000:afq=1.0:bd=preordered:fsr=off:fde=none:lma=on:nwc=1:sos=all:sp=occurrence:uhcvi=on_300");
    fallback.push("ott+1_3_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bsr=on:cond=fast:fsr=off:gs=on:gsem=on:nwc=1:nicw=on:sas=z3:sos=all:sp=occurrence:uhcvi=on_300");
    fallback.push("lrs+11_6_aac=none:add=off:afp=100000:afq=1.1:amm=off:anc=none:bd=off:fsr=off:gs=on:gsem=off:nwc=1:sas=z3:sp=occurrence_300");
    fallback.push("dis+11_2_av=off:gs=on:gsem=on:irw=on:nwc=1:sd=2:ss=axioms:st=1.5:sos=all:sp=reverse_arity_300");
    fallback.push("lrs+1011_8_add=large:afr=on:afp=40000:afq=1.2:amm=off:anc=none:bs=on:gs=on:gsem=off:nwc=1.5:nicw=on:sac=on:sp=reverse_arity:updr=off_300");
    fallback.push("dis-11_64_av=off:bd=off:bs=on:cond=on:fsr=off:nwc=1:sd=1:ss=axioms:urr=ec_only:updr=off_300");
    fallback.push("lrs+11_1024_add=off:afp=10000:afq=1.0:anc=none:bd=off:fsr=off:gs=on:gsem=on:irw=on:nwc=1.5:sas=z3:sp=occurrence:updr=off_300");
    fallback.push("lrs-11_3_aac=none:acc=on:afr=on:afp=10000:afq=1.1:bd=off:bs=unit_only:ccuc=first:irw=on:lcm=predicate:lma=on:nwc=1.5:sos=all:sac=on:sp=occurrence:updr=off_300");
    fallback.push("dis-10_3:1_add=large:afr=on:afp=1000:afq=2.0:anc=none:cond=fast:fsr=off:fde=none:gs=on:gsem=off:irw=on:lcm=reverse:lma=on:nwc=1:sas=z3:sd=2:ss=axioms:st=2.0:sos=all:sac=on:sp=reverse_arity:urr=on:uhcvi=on_300");
    fallback.push("lrs+11_2:1_av=off:cond=fast:fde=none:gs=on:gsem=off:lwlo=on:nwc=2:sp=occurrence:updr=off:uhcvi=on_600");
    fallback.push("lrs+11_32_add=off:afp=10000:afq=1.1:anc=all:bs=unit_only:cond=fast:fde=none:gs=on:gsaa=from_current:irw=on:lma=on:nwc=1:nicw=on:sos=all:sac=on:sp=occurrence:updr=off:uhcvi=on_600");
    fallback.push("ott+11_1_afr=on:anc=none:cond=on:fsr=off:gs=on:gsem=on:lma=on:nwc=1:sac=on:sp=occurrence:updr=off:uhcvi=on_900");
    break;

  case Property::EPR:
    fallback.push("ott+10_64_add=off:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:lcm=predicate:lma=on:nwc=1:sac=on:sp=reverse_arity:urr=on_300");
    fallback.push("lrs+2_64_add=large:afp=40000:afq=1.1:bd=off:bs=on:bsr=on:bce=on:fde=unused:irw=on:lma=on:lwlo=on:nwc=1:uhcvi=on_300");
    fallback.push("fmb+10_1_av=off:fmbsr=1.6:fde=none:updr=off_3000");
    fallback.push("dis+4_5_afp=1000:afq=1.1:amm=off:anc=none:bd=off:gs=on:irw=on:lcm=predicate:lma=on:nwc=1:sas=z3:sos=all:sp=occurrence_300");
    fallback.push("lrs+1003_10_afp=4000:afq=1.2:amm=sco:anc=none:bd=off:bsr=on:br=off:bce=on:fde=unused:lma=on:nwc=1:nicw=on:sac=on:urr=on:updr=off:uhcvi=on_1200");
    fallback.push("dis+11_2:3_add=large:afp=10000:afq=1.2:anc=none:bd=off:bce=on:cond=fast:er=filter:fsr=off:fde=unused:gsp=on:nwc=5:sos=theory:sac=on:urr=on_300");
    fallback.push("ott-4_6_add=off:afr=on:afp=100000:afq=1.4:amm=sco:bs=on:fde=unused:gs=on:gsaa=full_model:gsem=on:irw=on:nwc=1:sas=z3:sac=on:updr=off:uhcvi=on_600");
    fallback.push("ott+11_50_aac=none:add=off:afp=1000:afq=1.4:anc=none:bs=unit_only:fde=none:gs=on:gsem=off:lma=on:nwc=1:sas=z3:sac=on:uhcvi=on_200");
    fallback.push("dis-11_32_av=off:bs=unit_only:gs=on:irw=on:lma=on:nwc=1:updr=off_300");
    fallback.push("ott+10_1_add=large:afp=1000:afq=1.2:amm=off:anc=none:bd=off:bs=on:fsr=off:gs=on:gsem=on:irw=on:lma=on:nwc=1:sas=z3:sp=occurrence:updr=off_300");
    fallback.push("ott+1_3_add=large:afp=10000:afq=1.4:amm=off:bd=preordered:bs=on:bsr=on:bce=on:cond=fast:fsr=off:fde=unused:gs=on:irw=on:lma=on:nwc=1:sas=z3:sp=reverse_arity:updr=off:uhcvi=on_300");
    fallback.push("lrs+1_5:1_add=off:afr=on:afp=4000:afq=1.1:amm=sco:anc=none:cond=on:gs=on:nwc=1.1:nicw=on:sas=z3:sos=theory:urr=on:updr=off_300");
    fallback.push("lrs+1_16_add=off:afp=100000:afq=1.0:amm=off:cond=fast:er=filter:lcm=predicate:lma=on:lwlo=on:nwc=2:nicw=on:sd=7:ss=axioms:st=5.0:sos=theory:sp=reverse_arity:urr=ec_only_600");
    fallback.push("dis+1011_5_add=large:anc=none:bd=preordered:cond=on:fsr=off:fde=unused:lma=on:nwc=1:sos=theory:sp=occurrence:updr=off_1800");
    fallback.push("lrs+1_8:1_add=off:anc=none:bd=preordered:br=off:bce=on:fsr=off:fde=none:nwc=1:nicw=on:sos=theory:sp=reverse_arity:urr=on_900");
    break;

  case Property::UEQ:
    fallback.push("lrs+10_7_av=off:ins=3:lwlo=on:nwc=1.1_1500");
    fallback.push("lrs+10_4:1_av=off:bd=preordered:fde=none:ins=3:lwlo=on:nwc=3:sp=reverse_arity_600");
    fallback.push("ott+10_12_awrs=converge:awrsf=64:av=off:bd=preordered:fde=unused:ins=3:nwc=1.5:sp=frequency:uhcvi=on_2100");
    fallback.push("lrs+10_3:1_awrs=decay:awrsf=512:av=off:fde=unused:ins=3:nwc=1:s2a=on:sp=frequency:uhcvi=on_1500");
    fallback.push("ott+10_5_av=off:ins=3:nwc=1.1:sp=occurrence_2100");
    fallback.push("ott+10_8_awrs=converge:awrsf=8:av=off:bd=preordered:ins=3:nwc=1:s2a=on_2100");
    fallback.push("ott+10_4_av=off:fde=none:ins=3:nwc=1:sos=on:sp=occurrence:uhcvi=on_300");
    fallback.push("lrs+10_2:1_av=off:bd=off:fde=none:ins=3:lwlo=on:nwc=1:uhcvi=on_900");
    fallback.push("ott+10_5:1_av=off:bd=preordered:fde=unused:ins=3:nwc=1_300");
    fallback.push("ott+10_20_av=off:ins=3:nwc=1.5:sp=reverse_arity:uhcvi=on_1200");
    fallback.push("ott+10_4_awrs=decay:awrsf=4:av=off:ins=3:nwc=1.2:sp=weighted_frequency:uhcvi=on_900");
    fallback.push("lrs+10_5:1_av=off:bd=off:ins=3:nwc=2.5:sp=reverse_arity_600");
    fallback.push("ott+10_8:1_awrs=converge:awrsf=8:av=off:bd=preordered:fde=unused:ins=3:nwc=1.2:sp=weighted_frequency:uhcvi=on_2400");
    fallback.push("lrs+10_4:1_awrs=converge:awrsf=1:av=off:bd=preordered:ins=3:lwlo=on:nwc=1.3:s2a=on:sp=weighted_frequency:uhcvi=on_1200");
    fallback.push("lrs+1011_8_av=off:bs=unit_only:ep=RSTC:gsp=on:gs=on:gsem=on:lwlo=on:nwc=1_300");
    fallback.push("ott+10_8_av=off:bd=preordered:ins=3:nwc=1.2:sp=reverse_arity:uhcvi=on_600");
    fallback.push("lrs+10_1024_awrs=converge:awrsf=256:av=off:fde=unused:ins=3:lwlo=on:nwc=1.3:sp=weighted_frequency:uhcvi=on_900");
    fallback.push("lrs+10_3:1_av=off:bd=preordered:fde=unused:ins=3:lwlo=on:nwc=1:sp=weighted_frequency_1500");
    fallback.push("lrs+10_128_awrs=converge:awrsf=16:av=off:bd=off:fde=unused:ins=3:lwlo=on:nwc=5:s2a=on:sp=frequency_1200");
    fallback.push("ott+10_40_av=off:bd=preordered:fde=none:ins=3:nwc=1.2:sp=weighted_frequency:uhcvi=on_1200");
    fallback.push("ott+10_8:1_av=off:bd=off:ins=3:nwc=1.5:sp=occurrence_1200");
    fallback.push("ott+10_6_av=off:bd=preordered:fde=none:ins=3:nwc=1.1:sos=on:sp=occurrence_900");
    fallback.push("lrs+10_4_awrs=decay:awrsf=512:av=off:bd=preordered:fde=unused:ins=3:nwc=2:sp=frequency:uhcvi=on_1200");
    break;

  case Property::FEQ:
    fallback.push("lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=on:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:sac=on:sp=occurrence_300");
    fallback.push("lrs+1_4_afp=100000:afq=1.2:anc=none:bd=off:cond=on:gs=on:gsem=off:nm=64:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:updr=off_300");
    fallback.push("dis+1002_4_add=large:afp=40000:afq=1.0:anc=none:cond=fast:fde=none:gs=on:gsaa=full_model:lma=on:lwlo=on:nm=0:nwc=1.5:sas=z3:sp=reverse_arity:tha=off:thi=strong_300");
    fallback.push("lrs+1011_2:1_av=off:irw=on:lwlo=on:nm=16:newcnf=on:nwc=2:sd=4:ss=axioms:st=3.0:sp=occurrence_300");
    fallback.push("lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:sp=occurrence_300");
    fallback.push("lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:sac=on_900");
    fallback.push("lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:sos=all:sp=reverse_arity:updr=off_300");
    fallback.push("dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_300");
    fallback.push("lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=on:gs=on:nm=16:nwc=1:sos=all:sp=occurrence:urr=on_300");
    fallback.push("lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence_300");
    fallback.push("dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_300");
    fallback.push("lrs+10_5:4_av=off:cond=on:fde=unused:gs=on:gsem=on:lcm=reverse:lma=on:lwlo=on:nm=32:nwc=1.7:sd=2:ss=axioms:st=2.0:sos=all_300");
    fallback.push("lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_300");
    fallback.push("lrs+1_1024_av=off:bs=on:fde=none:inw=on:irw=on:nm=64:nwc=1.2:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_600");
    fallback.push("lrs+11_1_av=off:bsr=on:gsp=on:gs=on:lcm=predicate:nm=64:nwc=1:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_300");
    fallback.push("dis+1010_2:3_add=off:afr=on:afp=10000:afq=1.1:anc=none:fsr=off:gs=on:gsem=off:nwc=1:sas=z3:sos=all:sac=on:sp=reverse_arity:tha=off_300");
    fallback.push("dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_300");
    fallback.push("lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:sp=occurrence:urr=on_300");
    fallback.push("lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=on:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_300");
    fallback.push("dis+11_32_av=off:ep=RST:fsr=off:lwlo=on:nm=6:nwc=1.1:sd=5:ss=axioms:st=5.0:sp=reverse_arity:uhcvi=on_1500");
    fallback.push("lrs+1002_8:1_av=off:cond=on:gsp=on:gs=on:irw=on:lma=on:nm=0:nwc=1.7:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_300");
    fallback.push("lrs+11_50_afp=100000:afq=1.1:amm=sco:anc=none:bs=unit_only:cond=on:irw=on:lma=on:nm=32:nwc=1.1:sp=reverse_arity_300");
    fallback.push("lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:sp=reverse_arity:updr=off_300");
    fallback.push("lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_300");
    fallback.push("dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_300");
    fallback.push("dis+1011_2:3_add=off:afr=on:afp=4000:afq=1.4:anc=none:bs=unit_only:fsr=off:gs=on:gsem=on:lwlo=on:nm=16:nwc=1.3:nicw=on:sas=z3:sac=on:tha=off_300");
    fallback.push("ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_300");
    fallback.push("dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=on:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_300");
    fallback.push("lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:sd=2:ss=axioms:st=1.5:sos=on_300");
    fallback.push("lrs+11_8:1_av=off:bd=off:bs=unit_only:gs=on:gsem=on:lma=on:lwlo=on:nm=0:nwc=1:sd=1:ss=axioms:sos=all:urr=on:updr=off_300");
    fallback.push("ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_300");
    fallback.push("ott+1002_128_av=off:bd=off:bs=on:bsr=on:cond=on:fsr=off:nm=6:newcnf=on:nwc=1:sp=reverse_arity:updr=off_300");
    fallback.push("ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_300");
    fallback.push("ott-11_3_add=large:afp=100000:afq=1.2:anc=none:bs=on:cond=fast:fde=none:gs=on:gsem=off:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sos=all:sp=occurrence:tha=off:urr=on:uhcvi=on_300");
    fallback.push("dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_300");
    fallback.push("lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:sp=occurrence:urr=on:updr=off_300");
    fallback.push("lrs-2_3:2_av=off:bce=on:cond=on:gsp=on:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_300");
    fallback.push("lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:sd=2:ss=axioms:st=1.5:updr=off_300");
    fallback.push("dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_300");
    fallback.push("lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:sos=on:sac=on:sp=reverse_arity:updr=off_300");
    fallback.push("lrs+1011_1_av=off:cond=on:gs=on:lma=on:nm=4:nwc=1:sd=3:ss=axioms:sos=all:sp=reverse_arity:updr=off_300");
    fallback.push("ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_600");
    fallback.push("lrs+1002_2:1_acc=on:add=large:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:ccuc=first:fsr=off:gs=on:irw=on:nm=32:newcnf=on:nwc=1:sd=2:ss=axioms:sos=on:sp=reverse_arity_300");
    fallback.push("ott+11_2:1_av=off:bd=off:bsr=on:br=off:cond=on:fsr=off:gsp=on:lma=on:nm=32:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("ott+11_3_afp=1000:afq=2.0:anc=none:fsr=off:irw=on:nwc=1.7:ss=axioms:st=1.5:sac=on:updr=off_300");
    fallback.push("dis+11_3_add=off:afp=10000:afq=2.0:amm=sco:anc=none:ep=RST:gs=on:gsaa=from_current:gsem=on:inw=on:nm=64:nwc=1:sd=10:ss=axioms:st=5.0:sos=all:tha=off:updr=off:uhcvi=on_300");
    fallback.push("ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=on:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_300");
    fallback.push("ott+1010_5:4_av=off:bd=off:fde=none:irw=on:lma=on:nm=32:nwc=2.5:sd=2:ss=axioms:st=3.0:urr=on_300");
    fallback.push("dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_300");
    fallback.push("ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_300");
    fallback.push("dis+1_3:1_acc=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:cond=on:fsr=off:gs=on:inw=on:lma=on:nm=32:nwc=1:urr=on_300");
    fallback.push("dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_300");
    fallback.push("lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=on:nm=6:newcnf=on:nwc=1:sos=all:sac=on:sp=reverse_arity:urr=ec_only_300");
    fallback.push("lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:sac=on:uhcvi=on_600");
    fallback.push("lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_300");
    fallback.push("dis+4_4_av=off:fsr=off:gs=on:lcm=reverse:lma=on:nm=4:newcnf=on:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence_300");
    fallback.push("dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_300");
    fallback.push("lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:sac=on:urr=on_300");
    fallback.push("dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=on:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_300");
    fallback.push("lrs+1002_3_av=off:cond=on:fsr=off:gs=on:gsem=off:lwlo=on:nm=64:nwc=2.5:sp=reverse_arity_300");
    fallback.push("dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_300");
    fallback.push("dis+1010_24_aac=none:afr=on:anc=none:cond=on:fsr=off:gs=on:gsem=on:nm=6:nwc=1:sas=z3:sos=on:sp=reverse_arity:tha=off_300");
    fallback.push("lrs+1002_1_av=off:er=filter:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.5:sos=on_300");
    fallback.push("dis-10_3:2_aac=none:afp=1000:afq=1.1:cond=on:fsr=off:lcm=reverse:lwlo=on:nm=16:nwc=1:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity:updr=off_300");
    fallback.push("dis+10_5_av=off:cond=on:gs=on:gsem=off:irw=on:lcm=predicate:lma=on:lwlo=on:nm=6:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence_300");
    fallback.push("lrs+1002_8:1_add=large:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:bsr=on:er=known:lwlo=on:nm=0:nwc=1.2:sd=1:ss=axioms:sp=occurrence:updr=off_300");
    fallback.push("dis+10_10_add=large:afp=4000:afq=1.1:amm=sco:anc=none:irw=on:lcm=reverse:lma=on:nm=6:nwc=1:sos=all:sac=on:sp=reverse_arity:urr=on_300");
    fallback.push("lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=on:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_300");
    fallback.push("lrs+1011_50_afr=on:afp=40000:afq=1.0:amm=off:anc=all_dependent:bs=on:bsr=on:bce=on:fde=unused:gs=on:lma=on:nm=16:nwc=1.1:sp=occurrence:updr=off_600");
    fallback.push("dis+1011_8:1_aac=none:acc=on:afp=1000:afq=1.4:amm=off:anc=all:bs=unit_only:bce=on:ccuc=small_ones:fsr=off:fde=unused:gsp=on:gs=on:gsem=off:lma=on:nm=16:nwc=2.5:sd=4:ss=axioms:st=1.5:sos=all:uhcvi=on_300");
    fallback.push("lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:sp=reverse_arity:updr=off_300");
    fallback.push("dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_300");
    fallback.push("lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:sos=all:updr=off_300");
    fallback.push("dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_300");
    fallback.push("lrs+10_2:3_aac=none:add=off:afr=on:afp=100000:afq=1.0:amm=sco:anc=none:bd=off:gs=on:gsem=on:inw=on:newcnf=on:nwc=1:sas=z3:sos=all:sp=reverse_arity:tha=off_300");
    fallback.push("lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:sac=on:uhcvi=on_300");
    fallback.push("lrs+2_3:1_afr=on:afp=10000:afq=1.0:amm=sco:anc=none:bs=unit_only:lcm=reverse:lma=on:nm=64:nwc=1.7:sas=z3:updr=off_300");
    fallback.push("lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_300");
    fallback.push("dis-10_4:1_aac=none:add=off:afp=1000:afq=1.4:amm=off:anc=none:cond=fast:ep=RSTC:gs=on:gsaa=from_current:gsem=on:inw=on:lma=on:nm=64:nwc=4:sas=z3:tha=off:thi=strong:uwa=interpreted_only:updr=off:uhcvi=on_300");
    fallback.push("lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_300");
    fallback.push("lrs+1_5:4_aac=none:add=off:afr=on:afp=4000:afq=1.2:amm=sco:anc=none:gsp=on:gs=on:irw=on:nm=64:newcnf=on:nwc=1.3:nicw=on:sas=z3:sp=occurrence:tha=off_300");
    fallback.push("lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:sos=theory:sp=occurrence:urr=ec_only:updr=off_300");
    fallback.push("lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:sos=on:urr=on_300");
    fallback.push("lrs+11_4_av=off:gsp=on:irw=on:lma=on:nm=0:nwc=1.2:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:sp=occurrence:updr=off_900");
    fallback.push("lrs+10_2:3_afp=1000:afq=1.1:amm=sco:anc=none:er=known:lcm=reverse:lwlo=on:nm=64:newcnf=on:nwc=2:sd=5:ss=axioms:sos=theory:sac=on:sp=occurrence_300");
    fallback.push("lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:sd=2:ss=axioms:st=3.0:urr=on:updr=off_300");
    fallback.push("lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:sp=occurrence:updr=off_300");
    fallback.push("ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_300");
    fallback.push("dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_300");
    fallback.push("ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_300");
    fallback.push("lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:sd=1:ss=axioms:st=2.0:sac=on:urr=on_300");
    fallback.push("ott+1_5:1_acc=on:add=off:afr=on:afp=100000:afq=1.1:amm=sco:anc=none:lcm=predicate:nm=16:nwc=1.1:sd=1:ss=axioms:st=3.0:sos=on:sac=on:updr=off_300");
    fallback.push("lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:sd=1:ss=axioms:sos=all:sp=occurrence_300");
    fallback.push("dis+1010_3:2_av=off:gsp=on:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_300");
    fallback.push("lrs-1_5:4_add=off:afp=100000:afq=1.4:amm=sco:anc=all_dependent:fde=none:gs=on:irw=on:lma=on:nm=0:nwc=1:sd=2:ss=axioms:sos=all:urr=ec_only_300");
    fallback.push("dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_300");
    fallback.push("lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=on:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:sp=occurrence:updr=off:uhcvi=on_300");
    fallback.push("dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_600");
    fallback.push("ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1200");
    fallback.push("dis+1002_4_add=off:afp=10000:afq=2.0:amm=off:anc=none:fsr=off:gsp=on:gs=on:gsem=on:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1:sos=on:sac=on:sp=occurrence:tha=off:updr=off_300");
    fallback.push("dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=on:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_300");
    fallback.push("ott+1011_3:1_aac=none:add=off:afp=1000:afq=1.2:amm=sco:bd=off:bs=on:bsr=on:cond=on:gsp=on:gs=on:lma=on:nm=6:newcnf=on:nwc=1.3:nicw=on:sd=3:ss=axioms:st=2.0:sp=reverse_arity:urr=ec_only:updr=off_300");
    fallback.push("dis+10_4_add=off:afr=on:afp=1000:afq=1.4:amm=sco:anc=none:fsr=off:gs=on:gsem=on:lcm=predicate:lma=on:nm=64:nwc=1:sd=3:ss=axioms:sos=on:sp=reverse_arity_300");
    fallback.push("lrs+1011_4:1_av=off:fsr=off:irw=on:nwc=1:sd=4:ss=axioms:st=1.5:sp=reverse_arity_300");
    fallback.push("dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=on:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_300");
    fallback.push("lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=on:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_300");
    fallback.push("dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_300");
    fallback.push("dis+11_3_afp=100000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:inw=on:lma=on:nm=64:nwc=1:sas=z3:sd=10:ss=axioms:st=5.0:sp=occurrence:tha=off:updr=off_300");
    fallback.push("dis+1010_2_afr=on:afp=1000:afq=1.1:amm=off:anc=none:bs=unit_only:bce=on:cond=fast:fsr=off:fde=none:gs=on:gsem=off:nm=0:nwc=5:nicw=on:sas=z3:sac=on:urr=ec_only:updr=off:uhcvi=on_300");
    fallback.push("lrs+1002_16_av=off:cond=on:nwc=3_300");
    fallback.push("lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_300");
    fallback.push("dis-3_5_av=off:cond=on:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1:sos=on:sp=reverse_arity_300");
    fallback.push("ott+1_8_av=off:bd=off:bs=on:cond=on:gsp=on:gs=on:gsem=off:irw=on:lcm=predicate:lwlo=on:nwc=1:sos=on_300");
    fallback.push("lrs+10_3_add=off:afp=40000:afq=1.4:amm=off:anc=none:cond=fast:fde=none:gsp=on:gs=on:gsaa=full_model:inw=on:lma=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:tha=off:updr=off_300");
    fallback.push("dis+1010_4_afp=10000:afq=1.2:anc=none:irw=on:lma=on:nm=64:nwc=10:sas=z3:sac=on:sp=reverse_arity:updr=off_300");
    fallback.push("dis-3_4_add=off:afp=40000:afq=1.1:amm=off:anc=none:bs=unit_only:cond=fast:fsr=off:gs=on:inw=on:lma=on:nm=64:nwc=1.5:nicw=on:sas=z3:sp=reverse_arity:tha=off:thf=on:uhcvi=on_300");
    fallback.push("ott-2_28_add=large:afp=40000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=16:newcnf=on:nwc=1:nicw=on:sp=occurrence:thf=on_300");
    fallback.push("dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_300");
    fallback.push("lrs+1011_14_av=off:fsr=off:irw=on:nwc=1:sos=on:sp=occurrence:urr=ec_only:updr=off_300");
    fallback.push("dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_300");
    fallback.push("dis+11_28_av=off:fsr=off:irw=on:lcm=predicate:nm=2:newcnf=on:nwc=5:sp=occurrence:urr=on:updr=off_300");
    fallback.push("lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_300");
    fallback.push("lrs+11_3_av=off:cond=on:er=filter:fsr=off:gsp=on:gs=on:gsem=off:lcm=reverse:newcnf=on:nwc=1:sd=5:ss=axioms:st=3.0:sp=reverse_arity:urr=ec_only_300");
    fallback.push("dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=on:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_300");
    fallback.push("lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:sac=on:urr=on_300");
    fallback.push("dis+11_3_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bd=preordered:bce=on:fsr=off:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1:sd=10:ss=axioms:st=5.0:sac=on:sp=occurrence:tha=off:urr=ec_only_300");
    fallback.push("lrs+1_3:2_aac=none:add=large:anc=all_dependent:bce=on:cond=fast:ep=RST:fsr=off:lma=on:nm=2:nwc=1:sos=on:sp=occurrence:urr=on:updr=off:uhcvi=on_300");
    fallback.push("lrs+1_7_av=off:cond=fast:fde=none:gs=on:gsem=off:lcm=predicate:nm=6:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:updr=off_300");
    fallback.push("lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_300");
    fallback.push("lrs+10_5:4_afr=on:afp=40000:afq=1.2:bd=off:gsp=on:gs=on:inw=on:nm=0:nwc=1:sas=z3:sos=all:sp=reverse_arity:tha=off:thf=on:urr=on_300");
    fallback.push("ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_300");
    fallback.push("dis+1002_8_add=large:afp=100000:afq=1.2:amm=off:bs=on:irw=on:nm=2:newcnf=on:nwc=1.1:sos=on:sp=reverse_arity:urr=ec_only:updr=off_300");
    fallback.push("dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_300");
    fallback.push("dis+11_6_add=large:afr=on:afp=100000:afq=1.2:amm=off:anc=none:cond=fast:gs=on:gsaa=from_current:gsem=off:irw=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sos=on:sp=occurrence:tha=off:thi=strong:updr=off_300");
    fallback.push("lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=1.2:sp=reverse_arity_300");
    fallback.push("dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=on:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_300");
    fallback.push("dis+1010_3:1_av=off:gsp=on:nm=6:nwc=1:sos=all:sp=occurrence_300");
    fallback.push("ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_300");
    fallback.push("dis+4_2_av=off:bs=on:fsr=off:gsp=on:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_300");
    fallback.push("dis+1010_4_add=off:afp=100000:afq=1.0:anc=none:fsr=off:gs=on:gsem=off:inw=on:irw=on:lma=on:nm=64:nwc=1:sas=z3:sos=on:sac=on:tha=off:thf=on_300");
    fallback.push("dis+1011_5_aac=none:add=large:afp=40000:afq=1.2:amm=off:anc=none:bd=off:fsr=off:gsp=on:inw=on:irw=on:lma=on:nm=64:nwc=1:sas=z3:sos=on:sp=occurrence:tha=off:updr=off_300");
    fallback.push("lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:sos=all:updr=off_300");
    fallback.push("lrs+4_1_acc=on:afr=on:afp=100000:afq=1.2:amm=sco:anc=none:bd=off:bs=on:bsr=on:ccuc=first:fsr=off:fde=unused:irw=on:lma=on:nm=0:nwc=1.3:sd=10:ss=axioms:st=3.0:sos=all:sp=occurrence:uhcvi=on_300");
    fallback.push("dis+1011_10_aac=none:add=large:afp=10000:afq=1.1:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=6:newcnf=on:nwc=2.5:sp=reverse_arity:updr=off_300");
    fallback.push("dis+10_5_add=off:afp=4000:afq=1.1:anc=none:cond=fast:ep=RSTC:fsr=off:gs=on:gsem=on:lwlo=on:nm=64:nwc=1:sp=reverse_arity:thi=all_300");
    fallback.push("ott-11_12_aac=none:afp=100000:afq=1.2:amm=sco:bs=on:bce=on:cond=fast:er=known:gs=on:gsaa=from_current:gsem=off:irw=on:nm=4:nwc=2:sas=z3:sos=all:sp=occurrence:urr=ec_only:updr=off_600");
    fallback.push("lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:sp=occurrence:urr=on:updr=off_300");
    fallback.push("ott+11_20_afr=on:afp=100000:afq=1.2:amm=off:anc=none:bs=unit_only:bsr=on:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1:nicw=on:sas=z3:sac=on:updr=off:uhcvi=on_300");
    fallback.push("ott+10_7_av=off:bd=preordered:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=unused:irw=on:lma=on:nm=32:nwc=1:sos=all:sp=reverse_arity:updr=off_300");
    fallback.push("dis+1011_3_afp=100000:afq=1.1:amm=off:anc=none:fsr=off:gsp=on:gs=on:irw=on:nm=6:nwc=1:sas=z3:sd=2:ss=axioms:sos=on:sac=on:sp=reverse_arity:updr=off_300");
    fallback.push("dis+10_5_av=off:bce=on:cond=on:gsp=on:gs=on:lcm=predicate:lma=on:nm=6:nwc=1:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_300");
    fallback.push("lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:sac=on:sp=reverse_arity:uhcvi=on_300");
    fallback.push("lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:sos=all:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("lrs-2_3:1_add=off:afr=on:afp=1000:afq=1.2:amm=sco:anc=all_dependent:bd=off:bs=unit_only:bsr=on:cond=on:fde=unused:gs=on:gsem=on:irw=on:lcm=reverse:nm=32:nwc=1.7:sas=z3:sos=all:sac=on_300");
    fallback.push("lrs+11_4:1_av=off:bd=off:br=off:cond=fast:fde=unused:irw=on:lcm=reverse:lma=on:lwlo=on:nm=4:nwc=1:sd=3:ss=axioms:sos=all:urr=on_600");
    fallback.push("ott+11_128_afp=4000:afq=1.1:anc=none:bs=unit_only:cond=on:gsp=on:lma=on:nm=4:nwc=1.5:sos=theory:sp=occurrence:updr=off_300");
    fallback.push("lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:sos=on:urr=on:updr=off_300");
    fallback.push("dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_300");
    fallback.push("dis+10_3:2_afr=on:afp=1000:afq=1.2:bd=off:irw=on:lcm=predicate:lwlo=on:nm=0:newcnf=on:nwc=2:sos=on:tha=off:thf=on:urr=ec_only_300");
    fallback.push("dis+1003_64_add=off:afr=on:afp=100000:afq=1.1:anc=none:cond=fast:fde=none:irw=on:nm=6:newcnf=on:nwc=1.3:uhcvi=on_300");
    fallback.push("lrs+10_128_acc=model:afp=100000:afq=2.0:anc=all_dependent:bs=on:bsr=on:cond=fast:er=filter:gs=on:gsem=off:lcm=reverse:lma=on:nm=32:nwc=3:sac=on:sp=occurrence:urr=ec_only_300");
    fallback.push("lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:sd=3:ss=axioms:sos=all:sp=reverse_arity_300");
    fallback.push("ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_300");
    fallback.push("lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_300");
    fallback.push("dis+11_3:1_add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:bd=off:bs=unit_only:irw=on:lcm=predicate:lma=on:nm=2:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence:updr=off_300");
    fallback.push("dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=on:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_300");
    fallback.push("dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_300");
    fallback.push("dis+11_8_add=off:afp=10000:afq=1.2:amm=off:anc=none:cond=fast:ep=R:gs=on:gsaa=from_current:gsem=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=4:sd=1:ss=axioms:sac=on:updr=off:uhcvi=on_300");
    fallback.push("lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:sp=occurrence:urr=ec_only_600");
    fallback.push("lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:sp=reverse_arity:uhcvi=on_900");
    fallback.push("dis+11_7_av=off:bd=preordered:bs=unit_only:bce=on:cond=fast:fsr=off:fde=unused:gs=on:irw=on:nm=32:nwc=1:sd=4:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_1200");
    break;

  case Property::FNE:
    fallback.push("dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_300");
    fallback.push("dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_300");
    fallback.push("dis+1_2_add=large:afr=on:afp=1000:afq=2.0:anc=none:gsp=on:lcm=predicate:nm=64:newcnf=on:nwc=5:sac=on:urr=ec_only:updr=off_300");
    fallback.push("dis+10_1_add=off:afp=40000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:irw=on:nm=64:nwc=1:sas=z3:sac=on_300");
    fallback.push("dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_300");
    fallback.push("lrs+1011_1024_add=large:afp=4000:afq=1.1:anc=none:br=off:fsr=off:gsp=on:lma=on:nwc=1:sos=on:urr=on_300");
    fallback.push("dis+10_50_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:gs=on:lma=on:nm=64:nwc=1:sas=z3:sos=on:sp=occurrence:thf=on:updr=off_300");
    fallback.push("lrs+4_32_add=large:afp=10000:afq=1.2:amm=sco:anc=none:cond=on:fsr=off:gsp=on:lcm=predicate:lma=on:nm=2:nwc=1:sac=on:sp=occurrence:urr=on_300");
    fallback.push("dis+11_3_afr=on:afp=4000:afq=1.4:anc=none:cond=on:fsr=off:gs=on:lcm=reverse:nm=64:nwc=1:sos=on:sp=reverse_arity_300");
    fallback.push("lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_300");
    fallback.push("lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:sp=occurrence:updr=off_1500");
    fallback.push("dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_300");
    fallback.push("ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_300");
    fallback.push("lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:sp=occurrence:urr=on:updr=off_300");
    fallback.push("ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_300");
    fallback.push("lrs+1011_40_add=off:afr=on:afp=4000:afq=1.2:amm=sco:cond=on:fsr=off:gsp=on:gs=on:gsaa=from_current:gsem=off:nm=64:nwc=1:sos=all:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_600");
    fallback.push("ott+11_3:2_afp=40000:afq=1.0:amm=sco:bs=unit_only:cond=on:fsr=off:gs=on:gsaa=full_model:lcm=reverse:nm=32:newcnf=on:nwc=5:nicw=on:sd=3:ss=axioms:sac=on:urr=on:updr=off_1200");
    break;
  }

  // add very long final fallback strategy
  fallback.push("dis+11_1_3600");
} // getCasc2019Schedule

void Schedules::getCascSat2019Schedule(const Property& property, Schedule& quick, Schedule& fallback)
{
  Property::Category cat = property.category(); // currently unused
  unsigned long prop = property.props();
  unsigned atoms = property.atoms();

  (void)prop; (void)atoms; // to make "unused warning" go away

  switch (cat) {
  case Property::FNE:
    quick.push("ott+10_128_av=off:bs=on:gsp=on:irw=on:lcm=predicate:lma=on:nm=0:nwc=1:sp=occurrence:urr=on:updr=off:uhcvi=on_4");
    quick.push("fmb+10_1_av=off:bce=on:nm=6_1461");
    quick.push("dis+10_3_add=large:afp=10000:afq=2.0:amm=sco:anc=none:cond=on:fsr=off:gsp=on:lma=on:nm=16:nwc=1:sac=on:updr=off_197");
    quick.push("dis+1_3_av=off:cond=on:nm=64:newcnf=on:nwc=1_87");
    quick.push("ott-3_5_awrs=decay:awrsf=128:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bce=on:cond=fast:lma=on:nm=64:newcnf=on:nwc=1.1:sas=z3:sp=frequency:updr=off_146");
    quick.push("ott+2_5_afp=4000:afq=2.0:anc=none:bce=on:fsr=off:gsp=on:lma=on:nm=32:nwc=1:sp=reverse_arity_315");
    break;
  case Property::FEQ:
    quick.push("ott+11_3_aac=none:afr=on:afp=4000:afq=1.4:amm=off:anc=all:bs=unit_only:bsr=on:bce=on:fde=unused:irw=on:nm=64:newcnf=on:nwc=1:nicw=on:sac=on:sp=reverse_arity:uhcvi=on_31");
    quick.push("fmb+10_1_av=off:fmbsr=1.6:lma=on:nm=64:nwc=3:sp=reverse_arity:urr=on_258");
    quick.push("ott-4_4_awrs=decay:awrsf=64:add=off:afr=on:afp=40000:afq=1.0:amm=off:bs=on:gs=on:gsaa=from_current:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sac=on:sp=frequency:updr=off_36");
    quick.push("ott+10_128_av=off:bs=on:gsp=on:irw=on:lcm=predicate:lma=on:nm=0:nwc=1:sp=occurrence:urr=on:updr=off:uhcvi=on_231");
    quick.push("dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_169");
    quick.push("ott-3_5_awrs=decay:awrsf=128:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bce=on:cond=fast:lma=on:nm=64:newcnf=on:nwc=1.1:sas=z3:sp=frequency:updr=off_60");
    quick.push("ott+11_3:1_afp=4000:afq=2.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:lma=on:nm=64:newcnf=on:nwc=1:updr=off_83");
    quick.push("ott+10_3:1_afp=1000:afq=2.0:anc=none:fde=none:gs=on:gsaa=full_model:irw=on:nm=64:nwc=1:sas=z3:sac=on:updr=off_68");
    quick.push("dis-3_5_awrs=decay:awrsf=2:add=off:afr=on:afp=100000:afq=2.0:amm=sco:anc=none:bs=unit_only:bce=on:fsr=off:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1:sp=frequency:updr=off:uhcvi=on_119");
    quick.push("lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_109");
    quick.push("ott+4_5_add=large:afr=on:afp=40000:afq=1.1:amm=sco:bd=off:bs=unit_only:bsr=on:gs=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:sp=reverse_arity_234");
    break;
  case Property::PEQ:
    quick.push("lrs+11_6_aac=none:add=off:afp=100000:afq=1.1:amm=off:anc=none:bd=off:fsr=off:gs=on:gsem=off:nwc=1:sas=z3:stl=30:sp=occurrence_271");
    quick.push("dis+11_5:4_add=large:afr=on:afp=1000:afq=2.0:amm=off:anc=none:lwlo=on:nwc=1:sas=z3:sac=on:sp=reverse_arity_36");
    quick.push("fmb+10_1_av=off:fmbsr=1.2:fde=unused:updr=off_1755");
    break;
  case Property::NEQ:
  case Property::UEQ:
  case Property::HEQ:
    quick.push("dis+11_3_afp=100000:afq=1.1:amm=sco:anc=none:fsr=off:gs=on:gsem=on:irw=on:lma=on:nwc=10:sac=on_2");
    quick.push("dis+10_3_av=off:ins=3:nwc=1:sp=reverse_arity_2");
    quick.push("fmb+10_1_av=off:fmbsr=1.5:updr=off_43");
    quick.push("fmb+10_1_av=off:fmbsr=1.6_1165");
    quick.push("fmb+10_1_av=off:fmbsr=2.0:fde=none:updr=off_1793");
    break;
  case Property::HNE:
  case Property::NNE:
    quick.push("fmb+10_1_av=off:fmbsr=1.1:updr=off_7");
    quick.push("fmb+10_1_av=off:fmbsr=1.4_57");
    quick.push("dis-1_3_av=off:cond=on:fsr=off:gs=on:gsem=on:nwc=1:updr=off_2");
    quick.push("dis+11_3_add=large:afp=1000:afq=1.4:amm=off:anc=none:gs=on:lma=on:nwc=1:sas=z3:sac=on:sp=occurrence:updr=off_218");
    break;
  case Property::EPR:
    if (atoms > 10000) {
      quick.push("lrs+2_64_add=large:afp=40000:afq=1.1:bd=off:bs=on:bsr=on:bce=on:fde=unused:irw=on:lma=on:lwlo=on:nwc=1:stl=30:uhcvi=on_50");
      quick.push("dis-4_4_add=large:afr=on:afp=1000:afq=1.4:anc=all_dependent:bs=unit_only:fde=none:gs=on:gsaa=from_current:lma=on:nwc=1.2:sac=on:updr=off_353");
      quick.push("fmb+10_1_av=off:fmbsr=1.6:fde=none:updr=off_2528");
    }
    else {
      quick.push("fmb+10_1_av=off:fmbsr=1.6:fde=none:updr=off_25");
      quick.push("ott+11_50_aac=none:add=off:afp=1000:afq=1.4:anc=none:bs=unit_only:fde=none:gs=on:gsem=off:lma=on:nwc=1:sas=z3:sac=on:uhcvi=on_12");
      quick.push("dis-1_64_acc=on:add=large:afp=100000:afq=1.1:anc=none:bd=preordered:ccuc=small_ones:gs=on:nwc=1:sac=on:sp=reverse_arity:uhcvi=on_11");
      quick.push("ott+10_64_add=off:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:lcm=predicate:lma=on:nwc=1:sac=on:sp=reverse_arity:urr=on_57");
      quick.push("ott+1_3_awrs=converge:awrsf=16:av=off:bd=off:bs=on:bce=on:cond=fast:gs=on:gsem=off:irw=on:lma=on:nwc=1.5:sas=z3:sp=weighted_frequency:updr=off:uhcvi=on_80");
      quick.push("dis+4_7_aac=none:afr=on:anc=none:bd=preordered:bce=on:cond=fast:fsr=off:fde=unused:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:nicw=on:sas=z3:sac=on:sp=reverse_arity:uhcvi=on_176");
      quick.push("ott+1_3_add=large:afp=10000:afq=1.4:amm=off:bd=preordered:bs=on:bsr=on:bce=on:cond=fast:fsr=off:fde=unused:gs=on:irw=on:lma=on:nwc=1:sas=z3:sp=reverse_arity:updr=off:uhcvi=on_90");
      quick.push("ott+10_1_add=large:afp=1000:afq=1.2:amm=off:anc=none:bd=off:bs=on:fsr=off:gs=on:gsem=on:irw=on:lma=on:nwc=1:sas=z3:sp=occurrence:updr=off_233");
    }
    break;
  }
  fallback.push("fmb+10_1_av=off:bce=on:fmbes=smt:fmbsr=1.4:fde=none:ile=on:updr=off_600");
  fallback.push("fmb+10_1_av=off:bce=on:fmbsr=1.3:nm=2:newcnf=on_1200");
  fallback.push("fmb+10_1_av=off:fmbsr=1.1:updr=off_300");
  fallback.push("fmb+10_1_av=off:fmbsr=1.6_1200");
  fallback.push("fmb+10_1_av=off:fde=unused:ile=on:irw=on:lcm=predicate:lma=on:nm=16:nwc=1.7:sos=all:sp=reverse_arity_300");
  fallback.push("fmb+10_1_av=off:fmbsr=1.5:updr=off_300");
  fallback.push("lrs+11_6_aac=none:add=off:afp=100000:afq=1.1:amm=off:anc=none:bd=off:fsr=off:gs=on:gsem=off:nwc=1:sas=z3:sp=occurrence_300");
  fallback.push("fmb+10_1_av=off:fmbsr=1.4_300");
  fallback.push("dis+11_5_add=large:afr=on:afp=1000:afq=1.0:anc=none:bsr=on:fsr=off:nm=64:newcnf=on:nwc=1:updr=off_300");
  fallback.push("ott+11_3:1_afp=4000:afq=2.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:lma=on:nm=64:newcnf=on:nwc=1:updr=off_300");
  fallback.push("dis+4_7_aac=none:afr=on:anc=none:bd=preordered:bce=on:cond=fast:fsr=off:fde=unused:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:nicw=on:sas=z3:sac=on:sp=reverse_arity:uhcvi=on_300");
  fallback.push("fmb+10_1_av=off:fmbes=contour:fmbsr=1.6:ile=on:nm=64:updr=off_600");
  fallback.push("fmb+10_1_av=off:fmbsr=1.2:fde=unused:updr=off_1800");
  fallback.push("dis+11_1_afp=10000:afq=1.4:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nwc=1:sas=z3:sp=occurrence:updr=off_300");
  fallback.push("ott+10_6_add=off:afr=on:afp=1000:afq=1.0:amm=off:bsr=on:cond=on:fsr=off:fde=none:gs=on:gsem=on:ile=on:nm=2:newcnf=on:nwc=1:sp=reverse_arity:updr=off_300");
  fallback.push("ott+2_4:1_aac=none:add=off:afp=10000:afq=1.1:amm=off:anc=none:bs=on:gs=on:gsem=off:ile=on:irw=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=reverse_arity_300");
  fallback.push("ott+10_128_av=off:bs=on:gsp=on:irw=on:lcm=predicate:lma=on:nm=0:nwc=1:sp=occurrence:urr=on:updr=off:uhcvi=on_300");
  fallback.push("fmb+10_1_av=off:bce=on:nm=6_1500");
  fallback.push("ott+1_8:1_add=large:afp=10000:afq=1.0:amm=sco:anc=none:bd=off:bsr=on:fsr=off:fde=unused:ile=on:irw=on:nm=0:newcnf=on:nwc=1:sas=z3:sp=occurrence:updr=off:uhcvi=on_300");
  fallback.push("ott+11_3_afr=on:afp=10000:afq=1.4:amm=off:anc=none:bsr=on:cond=on:er=known:ile=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1:sac=on_300");
  fallback.push("dis+10_3_add=large:afp=10000:afq=2.0:amm=sco:anc=none:cond=on:fsr=off:gsp=on:lma=on:nm=16:nwc=1:sac=on:updr=off_300");
  fallback.push("lrs+1011_64_add=off:afr=on:afp=1000:afq=1.2:amm=off:anc=all_dependent:bsr=on:bce=on:cond=on:fsr=off:gs=on:inw=on:ile=on:nm=2:newcnf=on:nwc=1.1:sas=z3:sac=on:sp=occurrence:tha=off:thi=overlap:updr=off:uhcvi=on_300");
  fallback.push("dis+11_3_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bce=on:cond=on:fsr=off:ile=on:lwlo=on:nm=64:newcnf=on:nwc=1:sas=z3:tha=off:thf=on_300");
  fallback.push("dis+10_3_av=off:ins=3:nwc=1:sp=reverse_arity_300");
  fallback.push("fmb+10_1_av=off:fmbas=predicate:fmbes=contour:fmbsr=1.4:fde=unused:nm=64:newcnf=on:updr=off_600");
  fallback.push("fmb+10_1_av=off:fmbsr=2.0:fde=none:updr=off_1800");
  fallback.push("dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_300");
  fallback.push("dis-1_64_acc=on:add=large:afp=100000:afq=1.1:anc=none:bd=preordered:ccuc=small_ones:gs=on:nwc=1:sac=on:sp=reverse_arity:uhcvi=on_300");
  fallback.push("ott+10_3:1_afp=40000:afq=1.4:amm=off:anc=none:bs=on:irw=on:nm=64:nwc=1:sac=on:sp=reverse_arity_600");
  fallback.push("ott+10_64_add=off:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:lcm=predicate:lma=on:nwc=1:sac=on:sp=reverse_arity:urr=on_300");
  fallback.push("dis+11_3_add=large:afp=1000:afq=1.4:amm=off:anc=none:gs=on:lma=on:nwc=1:sas=z3:sac=on:sp=occurrence:updr=off_300");
  fallback.push("fmb+10_1_av=off:bce=on:fmbsr=1.3:fde=none:nm=64:newcnf=on_900");
  fallback.push("dis+11_5:4_add=large:afr=on:afp=1000:afq=2.0:amm=off:anc=none:lwlo=on:nwc=1:sas=z3:sac=on:sp=reverse_arity_300");
  fallback.push("ott+10_1_add=large:afp=1000:afq=1.2:amm=off:anc=none:bd=off:bs=on:fsr=off:gs=on:gsem=on:irw=on:lma=on:nwc=1:sas=z3:sp=occurrence:updr=off_300");
  fallback.push("ott+11_14_add=large:afp=1000:afq=1.4:amm=off:anc=none:fde=unused:gs=on:gsem=on:irw=on:nm=4:newcnf=on:nwc=1:sac=on:sp=occurrence_300");
  fallback.push("dis+4_16_acc=model:add=large:afr=on:afp=40000:afq=2.0:amm=off:anc=none:bs=on:ccuc=small_ones:fsr=off:ile=on:nm=4:newcnf=on:nwc=1:nicw=on:sp=reverse_arity_300");
  fallback.push("ott+2_6_add=large:afr=on:afp=4000:afq=2.0:amm=sco:anc=all:bs=on:bce=on:cond=fast:fde=none:gs=on:gsem=off:ile=on:nm=64:newcnf=on:nwc=1:sac=on:urr=on:updr=off_300");
  fallback.push("dis+1_3_av=off:cond=on:nm=64:newcnf=on:nwc=1_300");
  fallback.push("ott+1_3_add=large:afp=10000:afq=1.4:amm=off:bd=preordered:bs=on:bsr=on:bce=on:cond=fast:fsr=off:fde=unused:gs=on:irw=on:lma=on:nwc=1:sas=z3:sp=reverse_arity:updr=off:uhcvi=on_300");
  fallback.push("lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:sac=on:sp=occurrence_300");
  fallback.push("ott+4_5_add=large:afr=on:afp=40000:afq=1.1:amm=sco:bd=off:bs=unit_only:bsr=on:gs=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:sp=reverse_arity_300");
  fallback.push("ott+11_3_aac=none:afr=on:afp=4000:afq=1.4:amm=off:anc=all:bs=unit_only:bsr=on:bce=on:fde=unused:irw=on:nm=64:newcnf=on:nwc=1:nicw=on:sac=on:sp=reverse_arity:uhcvi=on_300");
  fallback.push("dis+11_50_aac=none:acc=model:add=large:afr=on:afp=4000:afq=2.0:anc=none:ccuc=first:er=known:fde=unused:gsp=on:gs=on:gsaa=full_model:ile=on:irw=on:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_300");
  fallback.push("ott+11_50_aac=none:add=off:afp=1000:afq=1.4:anc=none:bs=unit_only:fde=none:gs=on:gsem=off:lma=on:nwc=1:sas=z3:sac=on:uhcvi=on_200");
  fallback.push("ott+2_5_afp=4000:afq=2.0:anc=none:bce=on:fsr=off:gsp=on:lma=on:nm=32:nwc=1:sp=reverse_arity_600");
  fallback.push("dis-4_4_add=large:afr=on:afp=1000:afq=1.4:anc=all_dependent:bs=unit_only:fde=none:gs=on:gsaa=from_current:lma=on:nwc=1.2:sac=on:updr=off_600");
  fallback.push("fmb+10_1_av=off:bce=on:fmbes=contour:fmbsr=2.0:ile=on:nm=2_600");
  fallback.push("fmb+10_1_av=off:fmbsr=1.6:fde=none:updr=off_3000");
  fallback.push("fmb+10_1_av=off:bce=on:fmbes=smt:fmbsr=1.6:fde=none:ile=on:nm=64:updr=off_900");
  fallback.push("fmb+10_1_av=off:bce=on:fmbes=contour:fmbsr=1.4:fde=unused:updr=off_900");
} // getCascSat2019Schedule

void Schedules::getSmtcomp2018Schedule(const Property& property, Schedule& quick, Schedule& fallback)
{
  switch (property.getSMTLIBLogic()) {
  case SMT_AUFDTLIA:
  case SMT_AUFDTLIRA: // Add new logic here even though probably not best schedule
  case SMT_AUFDTNIRA: // Add new logic here even though probably not best schedule
    quick.push("lrs+1010_5:4_afp=100000:afq=1.2:anc=none:cond=on:fsr=off:ile=on:irw=on:nm=64:nwc=1:stl=30:sac=on:sp=occurrence:urr=on_9");
    quick.push("dis+11_5_add=large:afr=on:afp=10000:afq=1.2:anc=none:gs=on:gsem=on:ile=on:irw=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:sp=reverse_arity:urr=on:updr=off_273");
    quick.push("dis+1011_2:3_add=large:afr=on:afp=40000:afq=1.0:anc=none:br=off:cond=on:gs=on:gsem=on:ile=on:irw=on:lma=on:lwlo=on:nwc=1:sos=on:sac=on:sp=occurrence:tac=axiom:tar=off:urr=on:updr=off_264");
    break;

  case SMT_UFDTLIA:
  case SMT_UFDTLIRA: // Add new logic here even though probably not best schedule
  case SMT_UFDTNIA:
  case SMT_UFDTNIRA: // Add new logic here even though probably not best schedule
    quick.push("dis+1011_2:3_add=large:afr=on:afp=40000:afq=1.0:anc=none:br=off:cond=on:gs=on:gsem=on:ile=on:irw=on:lma=on:lwlo=on:nwc=1:sos=on:sac=on:sp=occurrence:tac=axiom:tar=off:urr=on:updr=off_2");
    quick.push("lrs+11_7_add=off:afr=on:afp=40000:afq=1.1:amm=off:anc=none:bsr=on:br=off:fde=unused:gs=on:gsem=on:inw=on:ile=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sac=on:urr=on:updr=off:uhcvi=on_5");
    quick.push("dis+1004_1_add=off:afr=on:afp=1000:afq=1.1:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=from_current:gsem=on:ile=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=occurrence:tac=light:tar=off:tha=off:thi=all:urr=on:uhcvi=on_6");
    quick.push("lrs+1010_5:4_afp=100000:afq=1.2:anc=none:cond=on:fsr=off:ile=on:irw=on:nm=64:nwc=1:stl=30:sac=on:sp=occurrence:urr=on_88");
    quick.push("lrs+10_2:1_add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bs=unit_only:cond=fast:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:ile=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:stl=30:sac=on:tac=axiom:tar=off:tha=off:uwa=ground:uhcvi=on_145");
    quick.push("lrs+1011_3:1_ind=struct:newcnf=on:ile=on:irw=on:lma=on:lwlo=on:sac=on:updr=off_10");
    break;

  case SMT_UFDT:
    quick.push("lrs+11_8:1_av=off:cond=on:fde=none:ile=on:nm=16:nwc=1.3:stl=30:sp=reverse_arity:urr=on:updr=off_135");
    quick.push("ott+1003_14_av=off:fsr=off:fde=unused:ile=on:lcm=predicate:nm=0:newcnf=on:nwc=1:sp=occurrence:uhcvi=on_12");
    quick.push("lrs+10_3:1_av=off:cond=on:fde=none:ile=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=reverse_arity:tar=off:uhcvi=on_148");
    quick.push("dis+1003_8_afr=on:anc=none:bd=preordered:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:sac=on:sp=reverse_arity:updr=off:uhcvi=on_271");
    quick.push("dis+1011_12_afp=100000:afq=1.0:amm=sco:anc=none:fsr=off:fde=unused:gsp=on:ile=on:irw=on:nm=64:nwc=1.2:sac=on:sp=occurrence:tac=axiom:tar=off:uhcvi=on_72");
    quick.push("dis+1011_4_add=large:afr=on:afp=4000:afq=1.4:anc=none:cond=on:ep=RS:fsr=off:gs=on:gsaa=from_current:ile=on:lwlo=on:nm=64:nwc=1:sos=all:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_145");
    quick.push("lrs+1010_5:4_afp=100000:afq=1.2:anc=none:cond=on:fsr=off:ile=on:irw=on:nm=64:nwc=1:stl=30:sac=on:sp=occurrence:urr=on_94");
    quick.push("lrs-1_3:1_av=off:bd=off:cond=on:gs=on:ile=on:lcm=reverse:lma=on:nm=32:nwc=1.2:stl=30:urr=on:updr=off_64");
    quick.push("lrs+11_8:1_add=large:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=fast:gs=on:gsaa=full_model:inw=on:ile=on:lcm=predicate:nm=4:newcnf=on:nwc=1:stl=30:sp=reverse_arity:tha=off:urr=on_201");
    quick.push("lrs+11_2:1_av=off:bd=off:br=off:bce=on:cond=on:fde=none:irw=on:lma=on:nm=2:newcnf=on:nwc=1.1:stl=30:sp=occurrence:urr=on:updr=off:uhcvi=on_228");
    quick.push("dis+1003_2:1_afr=on:afp=100000:afq=1.1:anc=none:cond=on:fde=unused:ile=on:lma=on:newcnf=on:nwc=1:sp=occurrence:tar=off:uhcvi=on_284");
    quick.push("dis+1011_2:3_add=large:afr=on:afp=40000:afq=1.0:anc=none:br=off:cond=on:gs=on:gsem=on:ile=on:irw=on:lma=on:lwlo=on:nwc=1:sos=on:sac=on:sp=occurrence:tac=axiom:tar=off:urr=on:updr=off_20");
    quick.push("dis+1_8:1_av=off:br=off:fsr=off:fde=none:gsp=on:ile=on:lma=on:nm=2:nwc=1:sos=on:sp=reverse_arity:urr=on:updr=off_13");
    quick.push("lrs+11_1_afr=on:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:cond=on:gsp=on:gs=on:ile=on:irw=on:nm=6:nwc=1:stl=30:sos=all:sac=on:urr=on_299");
    quick.push("lrs+10_3:2_av=off:bce=on:cond=on:er=filter:fsr=off:fde=unused:gs=on:gsem=on:ile=on:irw=on:nm=6:nwc=1:stl=30:sos=all:tac=light:tar=off:updr=off:uhcvi=on_10");
    quick.push("lrs+10_8:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:anc=none:bs=unit_only:ccuc=first:cond=on:er=known:gs=on:gsaa=from_current:ile=on:lcm=reverse:nm=2:nwc=1.2:stl=30:sac=on:urr=on:uhcvi=on_245");
    quick.push("lrs-11_4:1_afp=100000:afq=1.2:amm=off:anc=all_dependent:bs=unit_only:fsr=off:fde=none:gs=on:gsem=on:ile=on:lma=on:nm=64:nwc=1:stl=30:sp=reverse_arity:updr=off:uhcvi=on_232");
    quick.push("ott+1_8:1_add=large:afp=10000:afq=1.0:amm=sco:anc=none:bd=off:bsr=on:fsr=off:fde=unused:ile=on:irw=on:nm=0:newcnf=on:nwc=1:sas=z3:sp=occurrence:updr=off:uhcvi=on_90");
    quick.push("dis+1004_8_av=off:cond=on:er=filter:fde=unused:ile=on:lma=on:nm=64:newcnf=on:nwc=1:sp=reverse_arity_24");
    quick.push("lrs-11_4_acc=on:afr=on:afp=40000:afq=1.4:amm=off:anc=none:br=off:bce=on:cond=fast:fde=none:gs=on:ile=on:irw=on:nm=0:newcnf=on:nwc=1.1:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=on:updr=off_209");
    quick.push("dis+1011_1_av=off:fsr=off:fde=unused:gsp=on:ile=on:irw=on:lma=on:nwc=1:sos=on:sp=reverse_arity:urr=ec_only_89");
    quick.push("lrs+1_4_add=off:afp=100000:afq=2.0:anc=none:bsr=on:br=off:cond=on:fde=unused:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=2:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:urr=on:updr=off_122");
    quick.push("dis+1004_16_av=off:fsr=off:fde=unused:ile=on:irw=on:nm=0:newcnf=on:nwc=1.1:sp=reverse_arity:urr=on_191");
    quick.push("lrs+1011_3_add=large:afr=on:afp=100000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sac=on:tar=off_291");
    quick.push("dis-11_4:1_aac=none:add=large:afp=4000:afq=1.2:anc=none:fsr=off:ile=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1:sas=z3:sp=occurrence_99");
    quick.push("ott+1_5:1_afr=on:afp=4000:afq=1.2:amm=off:anc=none:bs=unit_only:br=off:cond=on:fsr=off:gs=on:gsem=on:ile=on:nm=64:newcnf=on:nwc=1:sac=on:sp=reverse_arity:urr=on:updr=off_573");
    quick.push("dis+1010_5_add=off:afp=100000:afq=1.0:amm=sco:anc=none:fsr=off:fde=none:gsp=on:gs=on:gsaa=from_current:ile=on:nm=64:nwc=1:sas=z3:tar=off:updr=off_5");
    quick.push("dis+1010_5_av=off:bsr=on:cond=fast:fde=unused:ile=on:nm=6:nwc=1:uhcvi=on_411");
    quick.push("dis+1010_1_av=off:ile=on:irw=on:nm=2:nwc=1:sas=z3:sp=occurrence:tar=off:urr=on_177");
    quick.push("lrs+11_1_add=off:afp=100000:afq=1.4:amm=off:anc=none:bsr=on:fsr=off:gs=on:ile=on:nm=64:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:updr=off_267");
    quick.push("lrs+10_5:1_av=off:fde=unused:ile=on:lwlo=on:nwc=1.1:stl=90:sp=occurrence:urr=on_343");
    break;

  case SMT_LIA:
    quick.push("dis+1011_8_afp=10000:afq=1.2:amm=sco:anc=none:bce=on:gs=on:gsem=off:ile=on:lma=on:nm=16:newcnf=on:nwc=2.5:sas=z3:sos=all:sac=on:sp=occurrence:updr=off_2");
    quick.push("dis+11_3_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bce=on:cond=on:fsr=off:ile=on:lwlo=on:nm=64:newcnf=on:nwc=1:sas=z3:tha=off:thf=on_2");
    quick.push("dis-2_4_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bce=on:gs=on:inw=on:ile=on:lwlo=on:nm=64:newcnf=on:nwc=1:sas=z3:sos=all:sp=reverse_arity:tha=off:thi=all_13");
    quick.push("dis+10_1_afp=10000:afq=1.0:amm=sco:anc=none:bce=on:fde=none:gs=on:gsem=off:inw=on:ile=on:irw=on:lma=on:nm=16:newcnf=on:nwc=1:sas=z3:sos=on:sac=on:sp=occurrence:tha=off:thi=full_145");
    quick.push("lrs+10_20_add=off:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bs=unit_only:bce=on:fde=unused:gs=on:gsaa=full_model:gsem=on:ile=on:nm=16:newcnf=on:nwc=1:sas=z3:stl=30:sp=occurrence:tha=off:thi=all:updr=off_87");
    quick.push("lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_1");
    break;

  case SMT_UFNIA:
    quick.push("lrs+11_5:4_av=off:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=32:newcnf=on:nwc=1.3:stl=30:sp=reverse_arity:updr=off_63");
    quick.push("ott+1010_7_av=off:fsr=off:fde=none:lma=on:nm=2:newcnf=on:nwc=1.3:sos=on:sp=reverse_arity:uhcvi=on_194");
    quick.push("dis+1011_8_av=off:bd=off:bsr=on:bce=on:cond=on:fsr=off:fde=unused:ile=on:nm=64:nwc=1.1:sd=10:ss=axioms:st=1.5:sos=all:sp=reverse_arity:tha=off_569");
    quick.push("dis+2_2_afr=on:afp=100000:afq=1.2:amm=off:anc=none:bsr=on:cond=on:gs=on:gsem=on:inw=on:ile=on:irw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=1.1:sas=z3:sac=on:tha=off:updr=off_47");
    quick.push("lrs-4_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:cond=on:fde=unused:gs=on:gsem=off:inw=on:ile=on:irw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sos=all:sp=occurrence:uwa=ground:urr=on:updr=off:uhcvi=on_132");
    quick.push("dis+10_2_add=off:amm=off:anc=none:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:ile=on:irw=on:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off:updr=off:uhcvi=on_75");
    quick.push("dis+1010_2:1_afp=40000:afq=1.1:anc=none:gsp=on:ile=on:irw=on:nm=6:nwc=1:sac=on:tha=off:updr=off_8");
    quick.push("lrs+1002_1_av=off:bd=off:fsr=off:fde=none:nm=2:newcnf=on:nwc=1:stl=30:sp=reverse_arity:uhcvi=on_26");
    quick.push("dis+10_3_add=large:afp=4000:afq=1.4:amm=off:anc=none:cond=on:ep=RS:gs=on:gsaa=from_current:inw=on:ile=on:lma=on:nm=2:newcnf=on:nwc=1:sac=on:tha=off:updr=off_3");
    quick.push("dis+1010_2:1_add=large:afp=10000:afq=2.0:amm=off:anc=all_dependent:bce=on:cond=fast:ep=R:fsr=off:ile=on:lma=on:nm=64:nwc=1:sac=on:urr=on_11");
    quick.push("lrs+1010_1_av=off:fde=unused:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_128");
    quick.push("dis+1010_1_afr=on:afp=40000:afq=2.0:amm=off:anc=none:gs=on:ile=on:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off_10");
    quick.push("dis+11_5:1_av=off:br=off:cond=on:fsr=off:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=0:newcnf=on:nwc=1:tha=off:urr=on_45");
    quick.push("ott+1002_5:1_add=large:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:br=off:cond=on:fsr=off:gs=on:inw=on:irw=on:lma=on:nm=0:newcnf=on:nwc=1:nicw=on:sos=all:tha=off:urr=on_74");
    quick.push("lrs+11_1_add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:fsr=off:gs=on:gsem=on:inw=on:ile=on:nm=64:newcnf=on:nwc=1:stl=30:sp=reverse_arity:tha=off:thf=on:updr=off_197");
    quick.push("lrs+11_2:1_afp=1000:afq=1.4:amm=off:anc=none:inw=on:ile=on:irw=on:nm=64:nwc=1:stl=30:sac=on:tha=off:urr=on_73");
    quick.push("dis+1002_2:3_av=off:bs=on:bce=on:cond=fast:ile=on:nm=2:newcnf=on:nwc=1:sp=occurrence:tha=off:thi=strong_79");
    quick.push("lrs+1011_3:1_add=off:afr=on:afp=4000:afq=2.0:amm=off:anc=none:bce=on:ep=RS:gs=on:ile=on:lma=on:nm=64:newcnf=on:nwc=1.2:stl=30:sp=occurrence:tha=off_5");
    quick.push("dis+11_2_afp=40000:afq=2.0:amm=off:anc=none:cond=on:fsr=off:gs=on:gsem=off:inw=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=occurrence:updr=off_12");
    quick.push("lrs+1010_1_add=off:afp=40000:afq=1.1:amm=off:anc=none:bd=off:fsr=off:inw=on:ile=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30:sp=occurrence_158");
    quick.push("dis+11_3_av=off:cond=on:fsr=off:ile=on:irw=on:nm=64:newcnf=on:nwc=1:sp=reverse_arity:tha=off:updr=off:uhcvi=on_117");
    quick.push("lrs+4_3_av=off:bd=preordered:fde=none:inw=on:ile=on:nm=64:newcnf=on:nwc=1:stl=30:tha=off:thf=on:updr=off:uhcvi=on_8");
    quick.push("lrs+1004_5:1_av=off:cond=on:fde=none:irw=on:lcm=reverse:lwlo=on:nm=64:newcnf=on:nwc=1:stl=60:sos=on:sp=reverse_arity:updr=off:uhcvi=on_215");
    quick.push("ott-1_3:1_av=off:bsr=on:br=off:bce=on:cond=on:fsr=off:fde=unused:irw=on:nm=2:newcnf=on:nwc=2.5:sos=on:sp=occurrence:tha=off:thi=overlap:urr=on:updr=off:uhcvi=on_148");
    quick.push("dis-1_128_av=off:bs=on:fde=unused:ile=on:irw=on:nm=32:nwc=1.1:sos=all:tha=off:thi=full:uwa=one_side_constant:uhcvi=on_355");
    quick.push("lrs+11_5:1_afr=on:afp=10000:afq=1.2:amm=off:anc=none:fsr=off:gs=on:inw=on:ile=on:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off_150");
    quick.push("lrs+1002_2:1_add=large:afp=100000:afq=1.2:amm=off:anc=none:cond=fast:fde=unused:gs=on:gsaa=from_current:gsem=on:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sd=5:ss=axioms:st=1.2:tha=off:uwa=ground_6");
    quick.push("dis+1002_1_av=off:bd=off:br=off:cond=on:fsr=off:fde=unused:newcnf=on:nwc=1:sd=5:ss=axioms:st=1.2:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_8");
    quick.push("lrs+1011_2:3_av=off:bsr=on:cond=fast:fsr=off:gsp=on:ile=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1:stl=30:tha=off:updr=off_87");
    quick.push("lrs+10_50_av=off:cond=fast:fde=none:lcm=reverse:nm=64:newcnf=on:nwc=1:stl=30:sp=occurrence:tha=off:uhcvi=on_264");
    quick.push("dis+1_4:1_acc=on:add=large:afp=4000:afq=1.2:amm=sco:anc=none:ccuc=small_ones:ile=on:lwlo=on:nm=64:nwc=1:tha=off:urr=ec_only:updr=off_228");
    quick.push("lrs+1010_8:1_av=off:br=off:cond=on:fsr=off:gsp=on:gs=on:gsem=off:inw=on:ile=on:irw=on:lma=on:nm=4:nwc=5:stl=30:sos=on:tha=off:thf=on:urr=on_44");
    quick.push("ott+1_5:1_av=off:bs=unit_only:br=off:gs=on:gsem=off:inw=on:ile=on:nm=64:newcnf=on:nwc=1:sd=4:ss=axioms:st=1.5:sp=occurrence:tha=off:urr=on:uhcvi=on_173");
    quick.push("ott+11_5:4_aac=none:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:bce=on:cond=on:fsr=off:fde=unused:ile=on:irw=on:lma=on:nm=6:newcnf=on:nwc=1:nicw=on:sas=z3:tha=off:updr=off_31");
    quick.push("lrs+1003_4:1_av=off:bd=preordered:cond=on:fde=unused:gs=on:ile=on:irw=on:nm=64:nwc=1.2:stl=90:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_322");
    quick.push("lrs+10_3_av=off:bs=unit_only:bce=on:cond=on:fde=unused:gsp=on:gs=on:inw=on:irw=on:nm=0:newcnf=on:nwc=1.1:stl=30:tha=off:uhcvi=on_44");
    quick.push("lrs+1002_8_afp=10000:afq=2.0:amm=sco:anc=none:bs=on:cond=on:fsr=off:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1.3:sas=z3:stl=30:sp=reverse_arity:urr=on_37");
    quick.push("lrs+1002_1_av=off:bd=off:bsr=on:cond=on:ile=on:lma=on:nm=64:nwc=1:stl=30:sos=on:sp=reverse_arity_18");
    quick.push("lrs-1_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sp=reverse_arity:tha=off:thf=on:urr=on_210");
    quick.push("ott+1011_4_afp=4000:afq=1.1:amm=off:anc=none:bs=unit_only:cond=fast:fsr=off:fde=none:gsp=on:ile=on:irw=on:nm=32:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off_45");
    quick.push("dis+1010_1_av=off:lma=on:newcnf=on:nwc=1:sd=4:ss=axioms:sos=on:sp=reverse_arity_196");
    quick.push("lrs+1002_5:4_add=large:afr=on:afp=40000:afq=2.0:anc=none:cond=on:inw=on:ile=on:nm=64:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:tha=off:updr=off_109");
    quick.push("lrs-11_4:1_aac=none:add=off:afp=10000:afq=1.2:anc=none:fsr=off:ile=on:lma=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:urr=on:updr=off_16");
    quick.push("lrs+10_5:4_av=off:bd=off:fsr=off:fde=none:lcm=reverse:lma=on:newcnf=on:nwc=1:stl=30:tha=off:urr=on:updr=off_173");
    quick.push("dis+1003_4:1_add=large:afp=10000:afq=1.4:amm=off:anc=none:bd=off:cond=fast:fsr=off:fde=none:gs=on:ile=on:lma=on:nm=64:nwc=1.2:sas=z3:sp=reverse_arity:tha=off:urr=ec_only_19");
    quick.push("dis+1002_1_afr=on:afp=1000:afq=1.1:amm=sco:anc=none:cond=on:fsr=off:ile=on:lma=on:nm=4:nwc=1:tha=off:updr=off_6");
    quick.push("dis+1010_6_av=off:cond=on:er=filter:fsr=off:nm=64:newcnf=on:nwc=1.3:sp=reverse_arity_222");
    quick.push("lrs+10_10_av=off:gs=on:gsem=on:inw=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.1:stl=30:updr=off_8");
    quick.push("lrs+2_8:1_add=off:afp=40000:afq=1.0:anc=none:fde=unused:gs=on:ile=on:irw=on:lcm=reverse:nm=64:nwc=3:sas=z3:stl=30:sp=occurrence:urr=on:uhcvi=on_13");
    quick.push("lrs+1011_10_av=off:cond=fast:er=filter:fsr=off:fde=none:gs=on:gsem=on:ile=on:lma=on:nm=4:nwc=1:stl=30:sos=all:sp=reverse_arity:tha=off:thi=new:uwa=ground:updr=off:uhcvi=on_118");
    quick.push("ott+1004_3_av=off:fde=none:gs=on:gsem=on:ile=on:nm=0:nwc=1.3:sp=reverse_arity:tha=off:thi=overlap:urr=ec_only:updr=off_106");
    quick.push("ott+11_2_av=off:inw=on:ile=on:irw=on:lcm=reverse:lma=on:nm=6:nwc=1.5:sp=occurrence:updr=off_158");
    quick.push("lrs+11_6_av=off:bd=off:cond=fast:fde=none:lma=on:lwlo=on:nm=0:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off:uhcvi=on_84");
    quick.push("ott+1_10_av=off:ep=RSTC:fsr=off:ile=on:lma=on:newcnf=on:nwc=1:sos=on:tha=off:updr=off_227");
    quick.push("dis+1003_28_acc=model:add=large:afp=10000:afq=1.1:amm=off:anc=none:bd=off:ccuc=first:fsr=off:gs=on:gsaa=from_current:ile=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence:tha=off:uwa=ground:uhcvi=on_86");
    quick.push("ott-1_24_av=off:bd=off:cond=fast:er=known:fsr=off:fde=unused:gsp=on:irw=on:lma=on:lwlo=on:nm=0:newcnf=on:nwc=1.3:sp=occurrence:tha=off:thi=new:uhcvi=on_88");
    quick.push("lrs+4_3:1_add=off:afp=1000:afq=2.0:anc=none:gs=on:gsem=on:ile=on:lma=on:nm=2:nwc=5:sas=z3:stl=30:sac=on:sp=occurrence:updr=off_8");
    break;

  case SMT_ALIA:
    quick.push("lrs+2_4_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bd=off:bce=on:fde=none:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:stl=30:tha=off:thi=strong:uwa=one_side_interpreted:urr=on:updr=off:uhcvi=on_3");
    quick.push("ott-3_2:3_add=off:afr=on:afp=40000:afq=1.0:bsr=on:cond=fast:fsr=off:fde=none:gs=on:ile=on:lma=on:lwlo=on:nm=2:newcnf=on:nwc=1.2:nicw=on:sas=z3:sos=all:sp=reverse_arity:urr=ec_only:updr=off_44");
    quick.push("lrs-1_128_aac=none:add=off:afp=40000:afq=1.0:amm=off:anc=none:fsr=off:inw=on:ile=on:lcm=reverse:lma=on:nm=16:nwc=10:sas=z3:stl=30:sac=on:updr=off_195");
    break;

  case SMT_UFLIA:
    quick.push("lrs-11_2:1_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:inw=on:ile=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.5:sas=z3:stl=30:sp=reverse_arity:urr=on_9");
    quick.push("lrs-10_3_av=off:bs=unit_only:bsr=on:cond=on:fsr=off:fde=unused:gs=on:inw=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.2:sas=z3:stl=30:tha=off:urr=ec_only_42");
    quick.push("lrs+1011_2:1_afr=on:afp=10000:afq=2.0:amm=off:gsp=on:gs=on:inw=on:ile=on:nm=2:nwc=1:sas=z3:stl=30:tha=off_296");
    quick.push("dis+10_14_add=large:afp=4000:afq=1.1:amm=sco:bs=unit_only:bsr=on:cond=fast:fde=none:inw=on:irw=on:lcm=predicate:nm=4:nwc=1.1:sos=on:sac=on:updr=off:uhcvi=on_268");
    quick.push("ott+1011_3:2_av=off:bd=off:bs=on:bce=on:cond=on:fde=unused:ile=on:lma=on:newcnf=on:nwc=1:tha=off:updr=off_124");
    quick.push("dis+1011_1_afp=40000:afq=1.2:anc=none:cond=on:gsp=on:ile=on:irw=on:lma=on:newcnf=on:nwc=1:sac=on:sp=occurrence:tha=off:updr=off_249");
    quick.push("lrs+1011_2:1_av=off:fsr=off:gs=on:gsem=off:inw=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:tha=off:urr=ec_only:uhcvi=on_79");
    quick.push("lrs+4_28_afp=10000:afq=1.2:amm=sco:anc=none:bd=off:bce=on:cond=on:fsr=off:ile=on:irw=on:lcm=reverse:nm=16:newcnf=on:nwc=2:sas=z3:stl=60:sp=occurrence:tha=off:updr=off:uhcvi=on_350");
    quick.push("lrs+4_8:1_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:ile=on:irw=on:lcm=reverse:lma=on:nm=2:nwc=1:stl=30:sos=all:tha=off_6");
    quick.push("ott+1011_8:1_afr=on:afp=1000:afq=1.4:amm=sco:anc=none:bd=off:fsr=off:fde=unused:inw=on:ile=on:nm=2:nwc=1:nicw=on:sas=z3:sos=theory:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_280");
    quick.push("lrs+11_2_av=off:cond=on:fsr=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:stl=30:sp=reverse_arity:tha=off:thf=on_66");
    quick.push("dis+1002_5:4_add=off:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fsr=off:inw=on:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:tha=off:updr=off_132");
    quick.push("lrs-11_8:1_afr=on:afp=1000:afq=1.4:amm=off:anc=none:bd=off:bs=on:gs=on:ile=on:lcm=predicate:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sp=occurrence:tha=off:thi=strong:uwa=interpreted_only_56");
    quick.push("lrs+4_4:1_add=off:afp=10000:afq=1.2:anc=none:bd=off:bsr=on:gs=on:gsem=on:inw=on:ile=on:irw=on:lma=on:nm=2:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off_1");
    quick.push("dis+1011_3:1_add=off:afr=on:afp=40000:afq=1.1:amm=sco:bd=off:bce=on:cond=fast:gsp=on:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=4:nwc=1.5:sas=z3:sos=all:sp=occurrence:tha=off:uwa=interpreted_only:uhcvi=on_93");
    quick.push("dis+1011_2_acc=on:afp=10000:afq=1.1:amm=sco:anc=none:ccuc=small_ones:cond=fast:fde=unused:lma=on:nm=64:newcnf=on:nwc=1:sac=on:sp=reverse_arity:tha=off:updr=off:uhcvi=on_267");
    quick.push("dis+10_2:1_aac=none:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:cond=on:fsr=off:gs=on:gsem=on:inw=on:ile=on:irw=on:nm=2:nwc=1.1:nicw=on:sas=z3:sos=theory:urr=on:updr=off_75");
    quick.push("dis+1010_2_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:bd=off:fsr=off:fde=none:ile=on:lcm=reverse:lma=on:nm=64:nwc=1:nicw=on:sas=z3:sp=reverse_arity_118");
    quick.push("lrs+2_4_add=large:afr=on:afp=100000:afq=1.1:amm=sco:anc=none:cond=on:ep=R:gs=on:gsaa=from_current:gsem=off:ile=on:lcm=reverse:lma=on:nm=2:nwc=1.1:stl=30:sos=on:sac=on:tha=off:updr=off_120");
    quick.push("ott+1010_2:1_add=off:afr=on:afp=1000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:ile=on:nm=64:newcnf=on:nwc=1:sd=2:ss=axioms:st=1.5:sac=on:tha=off:updr=off_193");
    quick.push("lrs+4_8:1_av=off:cond=on:gs=on:gsem=on:irw=on:nm=64:newcnf=on:nwc=1.1:stl=30:sp=occurrence:tha=off:urr=on:updr=off_133");
    quick.push("dis+1011_5:1_afp=4000:afq=1.4:amm=off:anc=none:cond=on:fde=unused:gsp=on:ile=on:lma=on:nm=16:nwc=1:sos=on:sac=on:tha=off:urr=ec_only:uhcvi=on_248");
    quick.push("lrs+11_5:1_add=off:afp=100000:afq=1.1:amm=off:anc=none:bd=off:cond=on:er=known:gs=on:gsem=off:inw=on:ile=on:irw=on:lcm=predicate:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sac=on:sp=reverse_arity:tha=off:thf=on_255");
    quick.push("dis-3_7_av=off:bs=unit_only:bsr=on:cond=on:fsr=off:fde=none:gsp=on:ile=on:irw=on:lma=on:nm=4:nwc=1:sos=all:sp=occurrence:tha=off:thi=overlap:uwa=interpreted_only:uhcvi=on_128");
    quick.push("lrs+1011_3:1_aac=none:add=large:afp=1000:afq=2.0:fsr=off:gs=on:gsaa=from_current:gsem=on:ile=on:nm=4:nwc=1.5:sas=z3:stl=30:sp=reverse_arity:tha=off:uwa=interpreted_only:uhcvi=on_158");
    quick.push("ott+1010_1_add=large:afp=1000:afq=1.2:anc=none:bd=off:ile=on:nm=2:newcnf=on:nwc=1:sp=occurrence:updr=off_221");
    quick.push("ott+10_4:1_aac=none:add=off:afp=40000:afq=1.1:amm=sco:anc=none:bd=off:gs=on:gsem=off:ile=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:sp=reverse_arity:tha=off:updr=off_210");
    quick.push("dis+1010_3_afp=10000:afq=2.0:amm=off:anc=none:cond=on:fsr=off:gs=on:gsem=off:inw=on:ile=on:irw=on:nm=64:nwc=1:sas=z3:tha=off:urr=on_46");
    quick.push("lrs+1002_2_add=large:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:inw=on:lwlo=on:nm=32:newcnf=on:nwc=1:stl=30:sos=theory:sac=on:sp=occurrence:urr=on_74");
    quick.push("ott+1011_3:1_add=off:afp=100000:afq=2.0:amm=off:anc=none:bs=unit_only:gs=on:gsem=on:irw=on:newcnf=on:nwc=1:sas=z3:tha=off_67");
    quick.push("lrs+2_1024_av=off:bd=off:bsr=on:cond=fast:fsr=off:fde=none:ile=on:irw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:stl=30:tha=off:thi=overlap:uwa=one_side_constant:updr=off:uhcvi=on_195");
    quick.push("lrs+1011_5:4_av=off:bd=off:bs=on:cond=on:er=known:gs=on:gsem=on:inw=on:ile=on:lcm=reverse:nm=6:newcnf=on:nwc=1:stl=30:sp=occurrence:tha=off:uhcvi=on_136");
    quick.push("lrs+11_2:1_add=off:anc=none:bsr=on:br=off:cond=on:er=filter:fsr=off:gs=on:gsem=on:inw=on:ile=on:lma=on:nm=2:nwc=1:sas=z3:stl=30:sos=all:sac=on:uwa=ground:urr=on_27");
    quick.push("dis+1011_8:1_add=off:afp=10000:afq=1.1:anc=none:bce=on:er=filter:gs=on:gsaa=from_current:gsem=off:inw=on:ile=on:lma=on:nm=2:nwc=3:sac=on:urr=on:updr=off_5");
    quick.push("dis+1_2_av=off:bd=off:cond=on:fsr=off:ile=on:irw=on:nm=64:newcnf=on:nwc=1:sp=reverse_arity:tha=off:urr=ec_only:updr=off_21");
    quick.push("dis-11_5:4_add=large:afp=40000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=fast:fsr=off:fde=unused:gsp=on:ile=on:lcm=reverse:lma=on:nm=6:nwc=1:sos=all:sac=on:urr=ec_only:uhcvi=on_72");
    quick.push("lrs-2_5:1_acc=on:add=off:afr=on:afp=40000:afq=1.1:amm=off:anc=none:bd=off:cond=fast:gs=on:ile=on:nm=0:newcnf=on:nwc=3:stl=30:sac=on:thf=on:urr=ec_only_296");
    quick.push("lrs+1011_3_add=off:afp=1000:afq=2.0:amm=off:anc=none:bsr=on:bce=on:cond=fast:fde=unused:ile=on:lma=on:nm=6:nwc=2:nicw=on:sas=z3:stl=30:sd=3:ss=axioms:st=2.0:sp=reverse_arity:tha=off_261");
    quick.push("dis+11_1_av=off:br=off:cond=on:gsp=on:gs=on:ile=on:lma=on:nm=2:newcnf=on:nwc=1:sp=reverse_arity:tha=off:urr=on_82");
    quick.push("lrs+1002_1_add=off:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:fsr=off:gsp=on:inw=on:ile=on:lcm=predicate:lwlo=on:nm=64:nwc=1.7:sas=z3:stl=30:sac=on:sp=reverse_arity:tha=off:thf=on_89");
    quick.push("ott+1011_2:3_add=large:afr=on:afp=40000:afq=2.0:anc=none:br=off:bce=on:cond=fast:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:newcnf=on:nwc=1.1:sp=reverse_arity:tha=off:urr=on:updr=off_148");
    quick.push("dis+11_7_add=large:afr=on:afp=10000:afq=1.2:bd=off:bsr=on:cond=on:fsr=off:fde=unused:gs=on:ile=on:lcm=predicate:lma=on:nm=2:newcnf=on:nwc=3:sos=on:sp=reverse_arity:tha=off:updr=off_22");
    quick.push("lrs+1_5:1_add=off:afr=on:afp=40000:afq=2.0:amm=off:anc=none:cond=on:gs=on:gsem=off:ile=on:lma=on:nm=64:nwc=1.2:stl=30:sp=reverse_arity_269");
    quick.push("ott+10_4:1_afp=100000:afq=1.1:anc=none:bd=off:inw=on:ile=on:irw=on:lma=on:nm=4:nwc=1:sos=all:sac=on:sp=occurrence:tha=off:urr=on:updr=off_6");
    quick.push("dis+11_5:1_afr=on:afp=40000:afq=2.0:amm=sco:anc=all_dependent:cond=fast:fde=unused:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=2:nwc=1:sos=all:urr=on:uhcvi=on_7");
    quick.push("dis+1002_1_add=large:afp=4000:afq=1.2:anc=none:cond=on:fsr=off:gs=on:gsem=off:ile=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:sp=occurrence:tha=off:thi=strong:uwa=interpreted_only:uhcvi=on_33");
    quick.push("ott+1011_5_av=off:fde=unused:gsp=on:gs=on:gsem=off:ile=on:nm=32:nwc=1.3:sas=z3:sp=reverse_arity:tha=off:uwa=ground_145");
    quick.push("lrs+10_24_av=off:bs=unit_only:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=60:sd=7:ss=axioms:st=1.2:sp=occurrence:tha=off:thf=on:uhcvi=on_343");
    quick.push("dis+1002_2_aac=none:add=off:afr=on:afp=100000:afq=1.2:amm=sco:anc=all:bsr=on:fde=unused:inw=on:ile=on:lcm=reverse:nm=4:nwc=4:nicw=on:sos=theory:sac=on:sp=reverse_arity:uhcvi=on_85");
    quick.push("ott+1002_2:1_add=large:afr=on:afp=100000:afq=1.1:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=from_current:irw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off:updr=off_90");
    quick.push("lrs+1003_3:2_afp=1000:afq=2.0:amm=off:anc=none:cond=on:gs=on:ile=on:lma=on:nm=6:newcnf=on:nwc=1:sas=z3:stl=30:sp=occurrence:tha=off:thi=all:updr=off_75");
    quick.push("lrs+1002_2:1_aac=none:add=large:afr=on:afp=40000:afq=1.1:amm=off:anc=none:cond=fast:gs=on:nm=64:newcnf=on:nwc=1.5:sas=z3:stl=30:sp=occurrence:updr=off_85");
    quick.push("dis+10_3_add=off:afp=100000:afq=1.4:amm=sco:anc=none:fsr=off:gs=on:gsem=on:inw=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sp=reverse_arity:tha=off:thf=on:updr=off_59");
    quick.push("lrs+11_10_add=off:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:bce=on:cond=fast:gsp=on:inw=on:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:tha=off:thf=on:urr=ec_only:uhcvi=on_44");
    quick.push("lrs+1002_8:1_add=off:afp=1000:afq=1.2:amm=sco:anc=none:bce=on:cond=on:ep=RS:gs=on:gsaa=from_current:ile=on:newcnf=on:nwc=1:sas=z3:stl=30:sp=occurrence:tha=off:uwa=interpreted_only:updr=off_199");
    quick.push("dis+1010_1_add=off:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:gs=on:gsem=off:inw=on:ile=on:irw=on:nm=6:nwc=1.3:nicw=on:sas=z3:tha=off:urr=ec_only_276");
    quick.push("dis+1011_4_afr=on:afp=10000:afq=1.1:amm=off:anc=none:ep=RS:fsr=off:ile=on:nm=64:newcnf=on:nwc=1:sos=all:sac=on:updr=off:uhcvi=on_55");
    quick.push("ott+1003_12_add=large:anc=all:bd=preordered:bce=on:fde=none:lcm=reverse:lma=on:nm=0:newcnf=on:nwc=1:nicw=on:sac=on:sp=reverse_arity:tha=off:uwa=ground_293");
    quick.push("lrs+1011_5:4_aac=none:add=off:afr=on:afp=1000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:bsr=on:cond=on:fde=none:gsp=on:gs=on:gsaa=from_current:gsem=on:inw=on:ile=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:tha=off:uwa=interpreted_only:uhcvi=on_146");
    quick.push("lrs+1011_2:1_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:bd=preordered:ccuc=first:cond=fast:fsr=off:fde=unused:inw=on:ile=on:irw=on:lma=on:nm=64:nwc=2:nicw=on:stl=30:sp=occurrence:urr=ec_only:updr=off_190");
    quick.push("lrs-11_4:1_add=large:afp=1000:afq=1.1:amm=sco:bs=on:cond=on:gs=on:gsem=on:ile=on:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sos=on:sp=occurrence:updr=off_128");
    quick.push("lrs-10_3:2_aac=none:add=off:afr=on:afp=4000:afq=1.4:amm=off:anc=none:bd=off:bsr=on:fsr=off:ile=on:irw=on:lcm=reverse:lma=on:lwlo=on:nm=16:nwc=1:nicw=on:sas=z3:stl=60:sd=2:ss=axioms:sos=on:sp=occurrence:updr=off_83");
    quick.push("ott+1011_3:1_aac=none:acc=on:afr=on:afp=4000:afq=1.2:amm=off:anc=none:bd=off:bs=on:bsr=on:ccuc=first:fsr=off:gs=on:gsem=on:inw=on:ile=on:nm=6:nwc=1:sos=on:thf=on:urr=on_20");
    quick.push("lrs+1010_3:1_av=off:bd=off:bsr=on:irw=on:nm=64:newcnf=on:nwc=1.7:stl=30:sos=all:updr=off_18");
    quick.push("lrs+11_8_afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=off:inw=on:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:stl=30:tha=off:urr=ec_only:updr=off_120");
    quick.push("lrs+1011_2:1_aac=none:add=off:afp=1000:afq=1.0:amm=off:bs=on:gs=on:gsaa=from_current:gsem=on:ile=on:lcm=reverse:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:stl=30:sp=reverse_arity:tha=off_200");
    quick.push("lrs+10_3:1_add=large:afp=10000:afq=1.1:amm=off:anc=none:cond=on:gs=on:gsem=off:inw=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sd=5:ss=axioms:st=1.5:tha=off:urr=on_183");
    quick.push("dis+10_3:2_add=large:afr=on:afp=1000:afq=1.1:anc=none:bd=off:fsr=off:inw=on:ile=on:lma=on:nm=2:nwc=1:sas=z3:sd=1:ss=axioms:sos=all:sp=occurrence:tha=off:updr=off_157");
    quick.push("lrs+1010_1_afp=1000:afq=1.4:amm=off:anc=none:bd=off:bsr=on:br=off:cond=on:ile=on:irw=on:nm=2:nwc=1:nicw=on:sas=z3:stl=30:sos=all:sp=reverse_arity:tha=off:urr=on:updr=off_48");
    quick.push("lrs-2_3:1_add=off:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:cond=on:er=filter:fde=unused:ile=on:irw=on:nm=64:newcnf=on:nwc=1.1:sas=z3:stl=60:sac=on:sp=reverse_arity:tha=off:thf=on:thi=strong:uhcvi=on_41");
    quick.push("dis+1011_3_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fde=none:gs=on:gsem=off:ile=on:lma=on:lwlo=on:nm=4:nwc=1:sac=on:tha=off:updr=off:uhcvi=on_205");
    quick.push("ott-1_1_acc=model:add=off:afr=on:afp=4000:afq=1.2:anc=all:bd=preordered:bs=unit_only:bsr=on:ccuc=first:gs=on:gsaa=from_current:ile=on:nm=64:newcnf=on:nwc=1:nicw=on:sac=on:sp=occurrence:tha=off:thi=strong:updr=off_80");
    quick.push("dis+1002_10_afp=4000:afq=1.4:amm=sco:bd=off:bsr=on:fsr=off:gs=on:gsem=off:inw=on:ile=on:nm=6:newcnf=on:nwc=1:nicw=on:sos=all:sp=occurrence:urr=ec_only_32");
    quick.push("ott+1011_5:4_aac=none:add=large:afp=100000:afq=2.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:cond=on:gs=on:inw=on:ile=on:irw=on:lma=on:nm=32:nwc=1:nicw=on:sas=z3:sos=on:sp=occurrence:tha=off:updr=off:uhcvi=on_305");
    quick.push("lrs+1_20_add=off:afp=40000:afq=1.4:anc=none:bd=off:bsr=on:gsp=on:inw=on:ile=on:newcnf=on:nwc=1:stl=30:sac=on:sp=reverse_arity:tha=off_23");
    quick.push("lrs+1004_1_aac=none:add=off:afr=on:afp=10000:afq=1.0:amm=sco:anc=all_dependent:bd=off:cond=fast:fsr=off:gs=on:gsaa=from_current:lcm=reverse:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sp=occurrence:tha=off:thf=on:urr=on:updr=off_16");
    quick.push("lrs+4_4_av=off:bd=off:bs=unit_only:cond=fast:fsr=off:fde=unused:gs=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1:stl=30:sp=occurrence:tha=off:thf=on:updr=off_234");
    quick.push("dis+1011_10_av=off:bd=off:cond=fast:er=known:inw=on:ile=on:irw=on:lma=on:nwc=1.7:sp=occurrence:tha=off:uhcvi=on_192");
    quick.push("lrs+10_3:1_afp=1000:afq=1.4:amm=off:anc=none:bsr=on:inw=on:ile=on:lma=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:tha=off:urr=on:updr=off_291");
    quick.push("dis+1011_5:1_afr=on:afp=10000:afq=1.2:amm=sco:bd=preordered:bs=unit_only:cond=on:fsr=off:inw=on:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=1.1:sd=7:ss=axioms:st=1.2:tha=off:uhcvi=on_267");
    quick.push("dis+2_1_add=large:afr=on:afp=1000:afq=1.2:anc=none:cond=on:nm=64:newcnf=on:nwc=1:tha=off:updr=off_49");
    quick.push("dis+10_4_afp=1000:afq=1.2:amm=sco:anc=none:gs=on:gsem=on:ile=on:irw=on:lcm=reverse:nm=64:newcnf=on:nwc=4:nicw=on:sas=z3_32");
    quick.push("dis+1002_14_av=off:cond=fast:fde=unused:inw=on:ile=on:lma=on:nm=0:nwc=1:sos=all:sp=reverse_arity:tha=off:uwa=one_side_interpreted:uhcvi=on_22");
    quick.push("dis+11_32_add=large:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:er=filter:ile=on:lcm=predicate:lma=on:newcnf=on:nwc=5:sp=occurrence:updr=off_286");
    quick.push("lrs+2_8_av=off:bsr=on:cond=on:fsr=off:ile=on:lma=on:nm=64:nwc=1.2:stl=30:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_171");
    quick.push("lrs+10_3_av=off:fde=unused:gs=on:gsem=on:inw=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1.7:stl=60:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_277");
    quick.push("lrs-10_5:4_add=off:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bd=off:bsr=on:cond=on:fsr=off:gsp=on:gs=on:ile=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:stl=30:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence_28");
    quick.push("dis+4_4:1_add=off:afp=4000:afq=1.2:amm=sco:anc=none:br=off:cond=fast:ep=RS:fsr=off:inw=on:lma=on:nm=2:newcnf=on:nwc=1:sp=reverse_arity:tha=off:thf=on:urr=on:uhcvi=on_29");
    quick.push("dis+1010_2_acc=on:afr=on:afp=100000:afq=1.2:anc=none:bsr=on:fsr=off:ile=on:irw=on:nm=16:newcnf=on:nwc=4:sp=occurrence:tha=off:urr=ec_only_202");
    quick.push("lrs+1002_1_aac=none:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ile=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sac=on:sp=occurrence:tha=off:updr=off_25");
    quick.push("lrs+2_3:2_av=off:cond=fast:inw=on:ile=on:nm=2:nwc=1:stl=30:sos=theory:urr=on_23");
    quick.push("ott-4_5:4_aac=none:afr=on:afp=100000:afq=1.2:amm=sco:anc=none:bd=off:bsr=on:br=off:cond=fast:ile=on:irw=on:lcm=reverse:lma=on:nm=64:newcnf=on:nwc=3:thf=on:urr=on:updr=off:uhcvi=on_171");
    quick.push("ott+1011_2:3_av=off:bs=unit_only:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:nm=2:newcnf=on:nwc=1:sp=reverse_arity:tha=off:thi=all:uwa=all:urr=on:uhcvi=on_225");
    quick.push("lrs+1011_2:3_aac=none:acc=on:add=large:afr=on:afp=40000:afq=1.2:amm=off:ccuc=small_ones:cond=fast:fsr=off:fde=none:gsp=on:gs=on:irw=on:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sp=occurrence:tha=off:thf=on:updr=off:uhcvi=on_32");
    quick.push("dis-4_7_acc=on:afp=40000:afq=1.4:anc=all_dependent:bsr=on:br=off:bce=on:ccuc=first:er=filter:fsr=off:fde=unused:gsp=on:ile=on:lcm=reverse:lma=on:nm=4:newcnf=on:nwc=1:nicw=on:sac=on:sp=reverse_arity:tha=off:thi=full:uwa=ground:urr=on:updr=off:uhcvi=on_12");
    quick.push("ott+10_2:1_av=off:bd=off:br=off:cond=fast:fsr=off:fde=none:gs=on:gsem=off:irw=on:nm=64:newcnf=on:nwc=1:sos=all:urr=on:updr=off:uhcvi=on_194");
    quick.push("dis+10_32_add=large:afp=40000:afq=1.0:anc=none:bd=off:bsr=on:fde=none:lma=on:nm=0:newcnf=on:nwc=1:nicw=on:sp=occurrence:tha=off:thi=full:uhcvi=on_202");
    quick.push("lrs+1011_8:1_av=off:bs=on:cond=on:fsr=off:inw=on:ile=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_117");
    quick.push("lrs+10_24_afp=4000:afq=2.0:bd=off:bsr=on:bce=on:cond=fast:fsr=off:gsp=on:gs=on:gsem=on:inw=on:ile=on:nwc=1.3:stl=30:sp=occurrence:tha=off:uwa=one_side_constant:urr=ec_only_282");
    quick.push("lrs+1011_8:1_add=off:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:fsr=off:gs=on:gsem=off:ile=on:irw=on:nm=2:nwc=1:sas=z3:stl=30:sp=reverse_arity:tha=off:urr=on:updr=off_7");
    quick.push("dis+2_4_afp=10000:afq=1.1:bd=off:bs=on:cond=on:er=filter:ile=on:newcnf=on:nwc=1:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_106");
    quick.push("lrs+1011_3_add=large:afp=10000:afq=1.1:amm=off:fde=unused:ile=on:irw=on:lma=on:nwc=1.7:stl=30:sp=reverse_arity:tha=off:thf=on:updr=off_218");
    quick.push("lrs+1010_1_add=large:afr=on:afp=40000:afq=2.0:anc=none:br=off:fsr=off:inw=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:stl=30:sos=all:urr=on_126");
    quick.push("lrs+10_2:3_afr=on:afp=1000:afq=1.1:bd=off:bce=on:cond=on:gsp=on:gs=on:gsaa=from_current:inw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sp=reverse_arity:tha=off:uwa=interpreted_only:updr=off:uhcvi=on_263");
    quick.push("dis+11_5:4_aac=none:acc=on:afp=40000:afq=2.0:amm=sco:anc=none:bd=off:cond=fast:fsr=off:fde=none:lcm=reverse:nm=2:newcnf=on:nwc=1.1:tha=off:thi=strong:uwa=interpreted_only:uhcvi=on_232");
    quick.push("lrs+1011_3:2_add=large:afp=10000:afq=1.4:amm=sco:anc=none:cond=fast:fde=unused:gsp=on:gs=on:ile=on:irw=on:lma=on:nwc=1:stl=30:sac=on:tha=off:updr=off:uhcvi=on_118");
    break;

  case SMT_UFIDL:
    quick.push("dis+11_3_add=large:afp=100000:afq=1.4:amm=off:anc=none:fsr=off:gs=on:ile=on:irw=on:lma=on:nm=32:nwc=1:tha=off:updr=off_2");
    quick.push("dis+10_3_afr=on:afp=1000:afq=1.0:anc=none:cond=on:fsr=off:gs=on:ile=on:irw=on:lwlo=on:nm=32:nwc=1:sos=all:sp=occurrence:urr=on_3");
    break;

  case SMT_LRA:
    quick.push("dis+1011_2:1_add=off:afp=40000:afq=1.1:amm=sco:anc=none:fsr=off:fde=unused:gsp=on:ile=on:irw=on:nm=64:newcnf=on:nwc=1.1:sas=z3:sos=all:sp=occurrence:updr=off:uhcvi=on_298");
    quick.push("dis+4_5_av=off:cond=on:fsr=off:gs=on:gsem=on:ile=on:irw=on:lwlo=on:nm=6:nwc=1:sos=on:sp=reverse_arity:updr=off_5");
    quick.push("ott+11_4_av=off:ile=on:lma=on:nm=64:nwc=1:sos=all:sp=occurrence:uwa=interpreted_only:updr=off:uhcvi=on_37");
    quick.push("dis+1_5:1_add=off:afp=40000:afq=1.2:anc=none:bd=off:cond=on:fsr=off:gs=on:ile=on:nm=64:nwc=4:sas=z3:updr=off_59");
    quick.push("dis+11_2_add=large:afr=on:afp=1000:afq=1.1:anc=none:gs=on:gsaa=full_model:ile=on:irw=on:lma=on:nm=16:nwc=1:sas=z3:sos=on:sac=on:sp=occurrence:thi=strong:uhcvi=on_72");
    break;

  case SMT_NIA:
    quick.push("dis+11_10_add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:cond=on:gs=on:gsem=on:inw=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=10:sas=z3:sac=on:sp=reverse_arity_2");
    break;

  case SMT_UFLRA:
    quick.push("dis+11_4_afp=4000:afq=1.4:amm=sco:anc=none:gs=on:ile=on:lma=on:nm=64:nwc=1.7:sas=z3:sac=on:sp=occurrence_2");
    break;

  case SMT_NRA:
    quick.push("dis+1011_4:1_anc=none:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:ile=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sac=on:sp=occurrence_9");
    quick.push("dis+11_2_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gs=on:ile=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sas=z3:sos=all:uwa=all:updr=off_2");
    quick.push("dis+11_3_afr=on:afp=40000:afq=2.0:anc=none:fsr=off:gs=on:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:sos=all:sac=on:sp=occurrence:urr=on_2");
    quick.push("dis+11_5_av=off:cond=on:fsr=off:ile=on:lwlo=on:nm=64:nwc=3:sp=reverse_arity:updr=off_4");
    quick.push("lrs+1011_3_add=large:afp=1000:afq=1.1:anc=none:cond=on:fsr=off:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:stl=30:sos=all:sac=on_182");
    break;

  case SMT_ANIA: // a newcomer ANIA, let's put it next to ALL
  case SMT_ALL: // Add ALL here as we don't currently have a  schedule for it and  this is better than just using fallback
  case SMT_AUFLIA:
  case SMT_AUFNIA:
    quick.push("lrs+1011_1_add=off:afr=on:afp=1000:afq=1.1:amm=off:anc=none:br=off:bce=on:er=filter:gsp=on:gs=on:gsaa=full_model:inw=on:ile=on:nm=32:nwc=1.2:sas=z3:stl=30:uwa=one_side_constant:urr=on_7");
    quick.push("dis+11_3_add=off:afp=1000:afq=2.0:amm=off:anc=none:fsr=off:gs=on:gsaa=full_model:inw=on:ile=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:sos=all:sp=occurrence:tha=off:uhcvi=on_13");
    quick.push("fmb+10_1_av=off:fde=unused:ile=on:irw=on:lcm=predicate:lma=on:nm=16:nwc=1.7:sos=all:sp=reverse_arity_2");
    quick.push("dis+1011_3:2_afp=1000:afq=1.2:anc=none:bd=off:fde=none:gsp=on:gs=on:gsaa=from_current:gsem=off:ile=on:irw=on:lma=on:lwlo=on:nm=6:nwc=1:nicw=on:sas=z3:sos=on:sac=on:sp=reverse_arity:urr=ec_only_11");
    quick.push("lrs+1011_12_afr=on:afp=100000:afq=1.4:amm=off:anc=none:cond=on:fsr=off:gs=on:ile=on:nm=64:nwc=1:sas=z3:stl=30:sac=on:tha=off:thf=on:urr=on_9");
    quick.push("dis+1011_3_add=large:afr=on:afp=10000:afq=1.0:anc=all_dependent:bd=off:cond=fast:gsp=on:ile=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1.3:nicw=on:sas=z3:sp=reverse_arity:updr=off_16");
    quick.push("dis-10_3_aac=none:acc=model:add=off:afp=100000:afq=1.1:anc=none:bs=unit_only:bce=on:ccuc=small_ones:cond=on:fsr=off:fde=none:gsp=on:ile=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=2:nwc=1.5:sos=on:sp=occurrence:uwa=ground:urr=ec_only:uhcvi=on_9");
    quick.push("lrs+1011_2_add=off:afr=on:afp=4000:afq=1.1:amm=off:bd=off:cond=fast:fde=none:gsp=on:gs=on:gsem=on:inw=on:ile=on:irw=on:nm=32:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:tha=off:urr=ec_only:uhcvi=on_4");
    quick.push("lrs+1_3:2_afr=on:afp=100000:afq=1.0:anc=all_dependent:cond=on:fde=none:gs=on:inw=on:ile=on:irw=on:nm=6:nwc=1:stl=30:sos=theory:updr=off:uhcvi=on_4");
    quick.push("lrs+10_14_add=large:afp=40000:afq=1.1:amm=sco:fde=unused:gs=on:gsem=on:ile=on:lma=on:nm=6:newcnf=on:nwc=1:nicw=on:stl=30:sp=reverse_arity:tha=off:uwa=one_side_interpreted:updr=off:uhcvi=on_28");
    quick.push("dis+11_3_afp=40000:afq=1.4:anc=none:bce=on:fsr=off:gs=on:gsaa=full_model:gsem=off:ile=on:lma=on:nm=64:nwc=1:uhcvi=on_20");
    quick.push("lrs+11_3_av=off:br=off:fsr=off:gs=on:inw=on:ile=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:uwa=one_side_interpreted:urr=on:updr=off:uhcvi=on_11");
    quick.push("lrs+1011_5:1_aac=none:add=off:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:bd=preordered:bsr=on:fde=none:gs=on:gsaa=from_current:inw=on:ile=on:irw=on:lcm=predicate:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:tha=off:uwa=ground:updr=off:uhcvi=on_46");
    quick.push("dis-4_4_add=large:afp=1000:afq=1.4:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=off:ile=on:irw=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:sp=reverse_arity:updr=off:uhcvi=on_10");
    quick.push("lrs+1011_8_aac=none:acc=model:add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:ccuc=first:cond=on:fde=none:gs=on:gsaa=from_current:inw=on:ile=on:nm=2:nwc=1:stl=30:sos=on:sp=reverse_arity:tha=off:urr=on_135");
    quick.push("lrs+1011_5_add=large:afp=1000:afq=1.2:amm=off:anc=none:br=off:fsr=off:gs=on:gsem=on:inw=on:ile=on:lma=on:nm=32:nwc=1:sas=z3:stl=30:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_9");
    quick.push("dis+1010_4_afp=40000:afq=1.1:amm=sco:anc=none:cond=fast:fde=none:gs=on:gsem=on:ile=on:irw=on:nm=4:nwc=1:sp=reverse_arity:uhcvi=on_140");
    quick.push("dis+11_4:1_add=large:afr=on:afp=40000:afq=1.1:amm=off:anc=none:br=off:cond=fast:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=2:nwc=1:sas=z3:ss=axioms:st=3.0:sos=all:sp=occurrence:tha=off:urr=on:updr=off:uhcvi=on_12");
    quick.push("lrs+10_5:1_afp=100000:afq=1.0:bd=preordered:inw=on:ile=on:irw=on:lcm=predicate:nm=6:nwc=1:stl=30:sos=all:sp=reverse_arity:tha=off:uwa=interpreted_only:urr=on:updr=off:uhcvi=on_255");
    quick.push("dis+11_8:1_afp=100000:afq=1.4:amm=sco:anc=none:cond=fast:fde=none:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=64:nwc=1:sos=all:sac=on:urr=on:uhcvi=on_145");
    quick.push("dis+1004_3_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:bs=unit_only:bsr=on:bce=on:ile=on:nm=64:newcnf=on:nwc=1:nicw=on:urr=ec_only_19");
    quick.push("dis+2_3_aac=none:afr=on:afp=1000:afq=1.1:bsr=on:cond=on:gs=on:gsem=off:lma=on:nm=64:nwc=1:sas=z3:sos=on:sp=occurrence:tha=off:thi=new:urr=ec_only:updr=off:uhcvi=on_23");
    quick.push("lrs+1011_64_add=off:afr=on:afp=1000:afq=1.2:amm=off:anc=all_dependent:bsr=on:bce=on:cond=on:fsr=off:gs=on:inw=on:ile=on:nm=2:newcnf=on:nwc=1.1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:thi=overlap:updr=off:uhcvi=on_129");
    quick.push("lrs+1003_2_av=off:cond=on:fsr=off:ile=on:nm=2:nwc=1.3:stl=30:sos=on:sp=occurrence:tha=off:updr=off:uhcvi=on_35");
    quick.push("lrs+1010_2:3_aac=none:acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bs=unit_only:bce=on:ccuc=first:fsr=off:fde=unused:gs=on:gsem=off:ile=on:nm=4:nwc=1:stl=30:sos=on:sp=reverse_arity:uhcvi=on_148");
    break;

    
  case SMT_AUFNIRA:
    quick.push("dis+11_2_add=large:afp=1000:afq=1.1:anc=none:fsr=off:fde=none:ile=on:irw=on:lma=on:nm=64:nwc=1:sas=z3:sos=all:sac=on_5");
    quick.push("lrs+10_8_afr=on:afp=4000:afq=1.1:amm=sco:anc=none:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:stl=30:sac=on:tha=off:urr=on:updr=off_2");
    quick.push("dis+1002_5_add=large:afr=on:afp=4000:afq=1.4:amm=off:anc=none:fsr=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sos=all:sac=on:sp=occurrence:updr=off_6");
    quick.push("lrs+11_3_afr=on:afp=40000:afq=1.1:anc=none:fsr=off:gs=on:gsem=off:inw=on:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:stl=30:sos=all:sac=on:sp=occurrence:updr=off_2");
    quick.push("lrs+1002_3_afr=on:afp=40000:afq=2.0:anc=none:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:inw=on:ile=on:irw=on:lma=on:nm=2:nwc=1.1:nicw=on:sas=z3:stl=30:sac=on:updr=off:uhcvi=on_7");
    quick.push("lrs+1_3:2_aac=none:afr=on:afp=40000:afq=1.0:anc=none:bs=unit_only:lma=on:nm=64:newcnf=on:nwc=3:sas=z3:stl=30:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_15");
    quick.push("lrs+1_3:1_acc=model:add=large:afp=40000:afq=1.2:anc=none:bd=off:bsr=on:ccuc=first:fsr=off:inw=on:irw=on:lma=on:nm=64:newcnf=on:nwc=2:stl=30:sp=reverse_arity:updr=off_13");
    quick.push("dis+1011_24_av=off:fsr=off:inw=on:ile=on:irw=on:nm=64:nwc=1:sos=all:tha=off:updr=off_8");
    quick.push("lrs+10_24_av=off:bd=off:cond=on:gs=on:gsem=off:inw=on:ile=on:irw=on:nm=64:nwc=2.5:stl=30:sp=occurrence_3");
    quick.push("dis+11_4_add=large:afr=on:afp=40000:afq=1.0:anc=none:gs=on:gsem=off:ile=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sp=occurrence:tha=off:updr=off_2");
    quick.push("lrs+1010_24_afp=40000:afq=2.0:amm=off:anc=none:cond=fast:gs=on:gsem=off:inw=on:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:tha=off:thf=on:updr=off:uhcvi=on_2");
    quick.push("lrs+10_3:1_afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:ile=on:irw=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity_93");
    quick.push("lrs+11_5:1_add=large:afr=on:afp=1000:afq=1.0:amm=off:anc=none:bd=off:gs=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:urr=ec_only_192");
    quick.push("lrs+1004_2_av=off:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lwlo=on:nm=0:nwc=1:stl=30:sp=occurrence:tha=off:thi=new:updr=off:uhcvi=on_79");
    quick.push("lrs+11_2:1_add=large:afr=on:afp=1000:afq=1.4:anc=none:cond=fast:fsr=off:fde=unused:gs=on:gsaa=full_model:gsem=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.1:stl=30:tha=off:urr=on:uhcvi=on_246");
    quick.push("lrs+1011_8:1_av=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:stl=30:sp=reverse_arity:tha=off:thi=strong:uwa=ground:urr=on:updr=off_74");
    quick.push("lrs+1011_7_av=off:cond=on:gs=on:ile=on:nm=64:nwc=3:stl=30:updr=off_166");
    quick.push("lrs+10_24_add=off:afp=100000:afq=1.2:amm=sco:anc=none:cond=on:fsr=off:gs=on:ile=on:nm=64:nwc=1:stl=30:sp=occurrence:tha=off:thf=on_45");
    quick.push("lrs+1003_3:1_av=off:bsr=on:cond=fast:fde=unused:inw=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sos=all:sp=occurrence:tha=off:updr=off:uhcvi=on_125");
    quick.push("ott+1004_8:1_afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:fde=unused:ile=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sp=reverse_arity:tha=off:updr=off_146");
    break;

  case SMT_UF:
    quick.push("lrs+11_5_av=off:cond=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:updr=off_22");
    quick.push("fmb+10_1_av=off:fmbes=contour:fmbsr=1.5:ile=on:updr=off_28");
    quick.push("dis+11_50_add=large:afp=10000:afq=1.2:anc=none:fsr=off:gs=on:gsem=off:ile=on:irw=on:nm=64:newcnf=on:nwc=1:sac=on_4");
    quick.push("dis+1010_5:1_av=off:cond=on:gsp=on:gs=on:gsem=on:irw=on:lma=on:nm=0:newcnf=on:nwc=1:urr=on:updr=off_74");
    quick.push("ott+11_1_add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:cond=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sp=occurrence:urr=ec_only_149");
    quick.push("lrs+10_128_add=off:afr=on:amm=sco:anc=none:bsr=on:cond=on:ile=on:irw=on:nm=2:nwc=2:nicw=on:sas=z3:stl=30:updr=off_96");
    quick.push("dis+4_16_acc=model:add=large:afr=on:afp=40000:afq=2.0:amm=off:anc=none:bs=on:ccuc=small_ones:fsr=off:ile=on:nm=4:newcnf=on:nwc=1:nicw=on:sp=reverse_arity_13");
    quick.push("dis+1010_2:1_add=off:afp=10000:afq=2.0:anc=none:cond=on:fde=none:gs=on:gsaa=from_current:gsem=off:ile=on:irw=on:lma=on:lwlo=on:nm=2:nwc=1:sas=z3:sp=occurrence:uhcvi=on_233");
    quick.push("lrs+11_4:1_av=off:bd=off:bs=unit_only:cond=on:fsr=off:fde=none:ile=on:irw=on:lwlo=on:nm=4:nwc=1.1:stl=30:sp=reverse_arity_127");
    quick.push("ott-10_4_av=off:bd=preordered:fsr=off:fde=none:ile=on:irw=on:nm=2:newcnf=on:nwc=1:updr=off:uhcvi=on_244");
    quick.push("lrs+1010_1_add=off:afp=1000:afq=1.0:amm=sco:anc=none:cond=on:fsr=off:gsp=on:gs=on:ile=on:lwlo=on:nm=64:newcnf=on:nwc=1:sas=z3:stl=30:sp=occurrence_192");
    quick.push("ott+1003_5_av=off:bd=off:bs=on:er=known:fde=none:gs=on:gsem=off:ile=on:nwc=2.5:sos=all:sp=occurrence:urr=on_237");
    quick.push("dis+1011_4:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bsr=on:fsr=off:ile=on:nm=64:nwc=5:sas=z3:sp=reverse_arity:urr=ec_only:updr=off_182");
    quick.push("dis+10_1_add=off:afp=4000:afq=1.4:amm=sco:anc=none:cond=on:ep=RSTC:gs=on:gsem=on:ile=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sos=on:sac=on:sp=reverse_arity_3");
    quick.push("lrs+10_5_add=off:afp=10000:afq=1.0:amm=off:anc=none:bsr=on:fde=unused:gs=on:irw=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:updr=off:uhcvi=on_283");
    quick.push("fmb+10_1_av=off:bce=on:fmbes=contour:fmbsr=1.4:fde=unused:updr=off_808");
    quick.push("dis+1011_8_av=off:bd=off:bs=unit_only:bsr=on:cond=on:irw=on:nm=64:newcnf=on:nwc=1_250");
    quick.push("dis+10_4:1_afp=10000:afq=1.4:anc=none:bd=off:fsr=off:gsp=on:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=reverse_arity:urr=on:updr=off_222");
    quick.push("lrs+10_3:1_afr=on:afp=100000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:ile=on:nm=64:newcnf=on:nwc=1:stl=30:sac=on:urr=on:uhcvi=on_212");
    quick.push("ott+11_8:1_acc=model:add=off:afr=on:afp=100000:afq=2.0:amm=off:anc=none:ccuc=first:cond=on:fde=none:gs=on:gsaa=from_current:gsem=on:ile=on:lwlo=on:nm=2:nwc=1:sos=all:urr=on_155");
    quick.push("lrs+10_3:2_av=off:bd=off:bsr=on:cond=on:fsr=off:gs=on:gsem=off:nm=64:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:urr=on_278");
    quick.push("dis+2_3_acc=on:add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:bs=unit_only:br=off:ccuc=first:cond=on:er=filter:ile=on:nm=6:nwc=1:urr=on_53");
    quick.push("ott+2_4:1_aac=none:add=off:afp=10000:afq=1.1:amm=off:anc=none:bs=on:gs=on:gsem=off:ile=on:irw=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=reverse_arity_130");
    quick.push("lrs+1011_3:2_av=off:bd=off:bsr=on:cond=on:fsr=off:gsp=on:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=64:nwc=1.5:sas=z3:stl=30:sp=reverse_arity_222");
    quick.push("dis+11_24_acc=on:afr=on:amm=sco:bsr=on:cond=on:gsp=on:gs=on:gsem=on:irw=on:lma=on:newcnf=on:nwc=1:updr=off_8");
    quick.push("ott+11_3_afr=on:afp=10000:afq=1.4:amm=off:anc=none:bsr=on:cond=on:er=known:ile=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1:sac=on_2");
    quick.push("lrs+10_8:1_aac=none:afr=on:afp=100000:afq=1.0:amm=off:cond=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1.7:stl=30:sp=reverse_arity:urr=on:updr=off_91");
    quick.push("lrs+11_3:1_av=off:bsr=on:cond=on:fsr=off:ile=on:irw=on:lma=on:nm=64:nwc=1.1:stl=30:sp=reverse_arity:updr=off_22");
    quick.push("lrs+1002_3_av=off:bs=unit_only:bsr=on:ile=on:nm=64:nwc=1:stl=30:sos=theory:sp=reverse_arity_273");
    quick.push("lrs-1_2:3_aac=none:add=off:afr=on:afp=40000:afq=2.0:amm=off:cond=on:fsr=off:fde=none:gs=on:gsaa=from_current:ile=on:irw=on:lwlo=on:nm=2:nwc=1.2:stl=60:sos=theory:sp=occurrence_120");
    quick.push("dis+11_50_aac=none:acc=model:add=large:afr=on:afp=4000:afq=2.0:anc=none:ccuc=first:er=known:fde=unused:gsp=on:gs=on:gsaa=full_model:ile=on:irw=on:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_5");
    quick.push("dis+1011_8:1_av=off:ile=on:lma=on:nm=32:newcnf=on:nwc=1:sp=occurrence_161");
    quick.push("dis+10_3:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:bd=off:cond=on:ile=on:nm=2:nwc=2.5:sas=z3:sac=on:sp=occurrence_91");
    quick.push("dis+4_6_av=off:bd=off:bs=on:ile=on:irw=on:lma=on:nm=64:nwc=1_229");
    quick.push("lrs+11_2_add=large:afr=on:amm=sco:anc=none:bsr=on:gs=on:gsem=off:irw=on:lma=on:nm=16:newcnf=on:nwc=1:stl=30:sac=on:sp=occurrence:urr=on:updr=off_270");
    quick.push("dis+1002_5_av=off:cond=on:fsr=off:ile=on:nm=64:newcnf=on:nwc=1.1:sp=reverse_arity_20");
    quick.push("dis+11_5_add=large:afr=on:afp=1000:afq=1.0:anc=none:bsr=on:fsr=off:nm=64:newcnf=on:nwc=1:updr=off_3");
    quick.push("dis+1004_4:1_av=off:br=off:cond=on:ep=RST:fsr=off:ile=on:lma=on:nm=2:newcnf=on:nwc=1.1:sp=occurrence:urr=on_69");
    quick.push("lrs+1011_3:2_add=large:afp=100000:afq=1.1:anc=none:br=off:fsr=off:ile=on:irw=on:lwlo=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=occurrence:urr=on_1");
    quick.push("lrs+1011_1_av=off:bd=off:ile=on:irw=on:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1:stl=30:sp=occurrence_110");
    quick.push("lrs+11_3:2_av=off:cond=on:gs=on:gsem=off:ile=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:st=5.0:updr=off_78");
    quick.push("dis+1011_8:1_add=off:afp=10000:afq=1.0:amm=off:anc=none:bd=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sac=on:sp=reverse_arity:updr=off_91");
    quick.push("lrs+11_2_av=off:br=off:ep=R:ile=on:lma=on:nm=64:nwc=1:stl=30:urr=on_72");
    quick.push("ott+10_2:1_av=off:bce=on:cond=fast:fde=none:irw=on:nm=32:newcnf=on:nwc=1:sos=theory:updr=off_207");
    quick.push("ott+11_14_add=large:afp=1000:afq=1.4:amm=off:anc=none:fde=unused:gs=on:gsem=on:irw=on:nm=4:newcnf=on:nwc=1:sac=on:sp=occurrence_292");
    quick.push("dis+1010_4_av=off:bd=off:lma=on:nm=2:newcnf=on:nwc=1:sp=occurrence:updr=off_72");
    quick.push("ott+4_4_av=off:bd=off:er=filter:ile=on:irw=on:lma=on:nm=64:nwc=1:sos=on:sp=reverse_arity:updr=off_140");
    quick.push("dis+1_4_av=off:bd=off:fsr=off:nm=64:newcnf=on:nwc=1:sp=reverse_arity_243");
    quick.push("lrs+10_2:1_av=off:cond=on:fde=none:gs=on:gsem=off:ile=on:irw=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on_167");
    quick.push("dis+1011_2_acc=model:add=large:afp=40000:afq=1.0:anc=none:bd=off:bsr=on:ccuc=first:cond=on:er=known:fsr=off:ile=on:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence_132");
    quick.push("dis+1002_2_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:ep=RS:ile=on:nm=64:nwc=1:sac=on:sp=reverse_arity:uhcvi=on_81");
    quick.push("dis+2_4_acc=on:add=large:afp=100000:afq=1.1:amm=sco:anc=none:ccuc=first:cond=on:fsr=off:gs=on:ile=on:lcm=reverse:nm=64:newcnf=on:nwc=1.1:nicw=on_6");
    quick.push("lrs+1011_3:1_add=large:afr=on:afp=40000:afq=1.0:anc=none:cond=on:ile=on:irw=on:lma=on:lwlo=on:nm=64:nwc=1.1:sas=z3:stl=30:sac=on:updr=off_221");
    quick.push("fmb+10_1_av=off:bce=on:fmbes=contour:fmbsr=2.0:ile=on:nm=2_595");
    quick.push("ott+10_6_add=off:afr=on:afp=1000:afq=1.0:amm=off:bsr=on:cond=on:fsr=off:fde=none:gs=on:gsem=on:ile=on:nm=2:newcnf=on:nwc=1:sp=reverse_arity:updr=off_6");
    quick.push("lrs+1_32_av=off:bd=off:bs=unit_only:er=known:gsp=on:gs=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=on:sp=reverse_arity:urr=ec_only_88");
    quick.push("fmb+10_1_av=off:bce=on:fmbes=smt:fmbsr=1.6:fde=none:ile=on:nm=64:updr=off_848");
    quick.push("lrs+1010_8:1_add=off:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:gsp=on:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=64:nwc=2:stl=30:updr=off_128");
    quick.push("ott+1_5:1_afp=4000:afq=1.1:anc=none:bd=off:cond=on:ile=on:nm=64:nwc=1:sas=z3:sac=on:sp=reverse_arity:urr=on:updr=off_154");
    quick.push("ott+2_6_add=large:afr=on:afp=4000:afq=2.0:amm=sco:anc=all:bs=on:bce=on:cond=fast:fde=none:gs=on:gsem=off:ile=on:nm=64:newcnf=on:nwc=1:sac=on:urr=on:updr=off_4");
    quick.push("fmb+10_1_av=off:bce=on:fmbsr=1.3:fde=none:nm=64:newcnf=on_761");
    quick.push("lrs+1002_3_acc=on:amm=sco:anc=none:ccuc=small_ones:gs=on:gsem=on:ile=on:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:stl=30:urr=on_295");
    quick.push("ott+1011_8:1_add=off:afr=on:afp=40000:afq=1.2:amm=off:anc=none:bd=off:fsr=off:ile=on:nm=64:newcnf=on:nwc=1.1:sas=z3:sp=reverse_arity:updr=off_55");
    break;

  case SMT_AUFLIRA:
    quick.push("lrs+1010_2_anc=none:fsr=off:gs=on:irw=on:newcnf=on:nwc=1:sas=z3:stl=30:sos=on:sp=occurrence:updr=off_4");
    quick.push("lrs+1010_4_av=off:bd=off:bs=unit_only:bsr=on:gs=on:inw=on:ile=on:lma=on:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_6");
    quick.push("dis+2_3_add=off:afp=40000:afq=1.1:anc=none:cond=on:gs=on:inw=on:ile=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:sp=reverse_arity:tha=off:urr=on:updr=off_43");
    quick.push("dis+1011_4_afr=on:afp=4000:afq=1.4:anc=none:fsr=off:gs=on:gsem=on:ile=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:tha=off:updr=off_8");
    quick.push("lrs+1010_20_add=large:afr=on:afp=4000:afq=1.4:amm=sco:anc=none:bd=preordered:bs=unit_only:fsr=off:fde=unused:gs=on:ile=on:lcm=reverse:nm=2:nwc=4:sas=z3:stl=120:sac=on:sp=occurrence:tha=off:urr=on:updr=off:uhcvi=on_791");
    quick.push("dis+1002_5:4_afr=on:afp=1000:afq=1.2:anc=none:cond=on:ile=on:irw=on:lwlo=on:nm=64:nwc=1:sas=z3:sac=on:sp=reverse_arity:tha=off:updr=off_33");
    quick.push("dis+1011_3_aac=none:afp=1000:afq=1.2:anc=all:fde=none:gs=on:gsem=on:inw=on:ile=on:lcm=predicate:lma=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:tha=off:urr=on_344");
    quick.push("dis+1011_32_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=sco:bs=on:bsr=on:br=off:fde=unused:gs=on:gsaa=full_model:ile=on:lcm=predicate:nm=6:newcnf=on:nwc=1.5:sas=z3:sos=all:sac=on:tha=off:thi=all:uwa=one_side_constant:urr=on_1");
    break;

  case SMT_QF_ABV:
  case SMT_QF_ALIA:
  case SMT_QF_ANIA:
  case SMT_QF_AUFBV:
  case SMT_QF_AUFLIA:
  case SMT_QF_AUFNIA:
  case SMT_QF_AX:
  case SMT_QF_BV:
  case SMT_QF_IDL:
  case SMT_QF_LIA:
  case SMT_QF_LIRA:
  case SMT_QF_LRA:
  case SMT_QF_NIA:
  case SMT_QF_NIRA:
  case SMT_QF_NRA:
  case SMT_QF_RDL:
  case SMT_QF_UF:
  case SMT_QF_UFBV:
  case SMT_QF_UFIDL:
  case SMT_QF_UFLIA:
  case SMT_QF_UFLRA:
  case SMT_QF_UFNIA:
  case SMT_QF_UFNRA:
    throw UserErrorException("Kein Kinderspiel, Bruder, use Z3 for quantifier-free problems!");

  case SMT_BV:
  case SMT_UFBV:
    throw UserErrorException("Sorry, we don't deal with bit-vectors!");
  case SMT_UNDEFINED:
    throw UserErrorException("This version cannot be used with this logic!");
  }

  fallback.push("dis+1002_5:1_aac=none:afr=on:afp=4000:afq=1.1:amm=sco:anc=none:bsr=on:br=off:cond=on:fsr=off:gsp=on:gs=on:gsem=on:inw=on:ile=on:irw=on:lma=on:nm=32:newcnf=on:nwc=1.1:sas=z3:sp=reverse_arity:tha=off:urr=on_600");
  fallback.push("lrs+1011_3:1_aac=none:add=large:afp=1000:afq=2.0:fsr=off:gs=on:gsaa=from_current:gsem=on:ile=on:nm=4:nwc=1.5:sas=z3:sp=reverse_arity:tha=off:uwa=interpreted_only:uhcvi=on_300");
  fallback.push("ott+1_5:1_afr=on:afp=4000:afq=1.2:amm=off:anc=none:bs=unit_only:br=off:cond=on:fsr=off:gs=on:gsem=on:ile=on:nm=64:newcnf=on:nwc=1:sac=on:sp=reverse_arity:urr=on:updr=off_600");
  fallback.push("dis+1011_4:1_anc=none:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:ile=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sac=on:sp=occurrence_300");
  fallback.push("lrs+10_5_add=off:afp=10000:afq=1.0:amm=off:anc=none:bsr=on:fde=unused:gs=on:irw=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=on:sac=on:sp=occurrence:updr=off:uhcvi=on_300");
  fallback.push("dis+10_4_add=off:afp=4000:afq=1.1:amm=sco:anc=none:fsr=off:gs=on:ile=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:tha=off:urr=on:updr=off_300");
  fallback.push("lrs-11_2:3_av=off:bd=off:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:sp=reverse_arity_600");
  fallback.push("lrs+1_3:1_acc=model:add=large:afp=40000:afq=1.2:anc=none:bd=off:bsr=on:ccuc=first:fsr=off:inw=on:irw=on:lma=on:nm=64:newcnf=on:nwc=2:sp=reverse_arity:updr=off_300");
  fallback.push("fmb+10_1_av=off:bce=on:fmbes=contour:fmbsr=1.4:fde=unused:updr=off_900");
  fallback.push("dis+1011_2:1_add=off:afp=40000:afq=1.1:amm=sco:anc=none:fsr=off:fde=unused:gsp=on:ile=on:irw=on:nm=64:newcnf=on:nwc=1.1:sas=z3:sos=all:sp=occurrence:updr=off:uhcvi=on_300");
  fallback.push("ott+1010_2:1_acc=on:add=large:afr=on:afp=40000:afq=1.1:anc=none:gs=on:inw=on:ile=on:nm=64:newcnf=on:nwc=1:sos=on:sac=on:sp=reverse_arity:urr=on_300");
  fallback.push("lrs+10_3:1_afr=on:afp=100000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:ile=on:nm=64:newcnf=on:nwc=1:sac=on:urr=on:uhcvi=on_300");
  fallback.push("dis+1002_3_add=off:afr=on:amm=off:anc=none:cond=on:ile=on:lma=on:nm=64:nwc=1:nicw=on:sac=on:sp=reverse_arity:tac=axiom:tar=off:updr=off_300");
  fallback.push("dis+2_1_add=large:afr=on:afp=1000:afq=1.2:anc=none:cond=on:nm=64:newcnf=on:nwc=1:tha=off:updr=off_300");
  fallback.push("lrs+10_20_add=off:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bs=unit_only:bce=on:fde=unused:gs=on:gsaa=full_model:gsem=on:ile=on:nm=16:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off:thi=all:updr=off_300");
  fallback.push("lrs+1002_5:4_add=large:afr=on:afp=40000:afq=2.0:anc=none:cond=on:inw=on:ile=on:nm=64:nwc=1:sas=z3:sd=10:ss=axioms:tha=off:updr=off_300");
  fallback.push("dis-11_7_add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:cond=on:fsr=off:ile=on:irw=on:nm=6:nwc=10:sas=z3:sp=occurrence:updr=off_300");
  fallback.push("fmb+10_1_av=off:fde=unused:ile=on:irw=on:lcm=predicate:lma=on:nm=16:nwc=1.7:sos=all:sp=reverse_arity_300");
  fallback.push("lrs+10_5:1_av=off:fde=unused:ile=on:lwlo=on:nwc=1.1:sp=occurrence:urr=on_900");
  fallback.push("ott+10_4:1_aac=none:add=off:afp=40000:afq=1.1:amm=sco:anc=none:bd=off:gs=on:gsem=off:ile=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:sp=reverse_arity:tha=off:updr=off_300");
  fallback.push("dis+1011_32_av=off:bd=off:inw=on:irw=on:lwlo=on:nm=16:nwc=3:sd=2:ss=axioms:st=5.0:sp=occurrence:tha=off_600");
  fallback.push("dis+1011_2_acc=on:afp=10000:afq=1.1:amm=sco:anc=none:ccuc=small_ones:cond=fast:fde=unused:lma=on:nm=64:newcnf=on:nwc=1:sac=on:sp=reverse_arity:tha=off:updr=off:uhcvi=on_300");
  fallback.push("lrs+1011_3:1_add=large:afr=on:afp=40000:afq=1.0:anc=none:cond=on:ile=on:irw=on:lma=on:lwlo=on:nm=64:nwc=1.1:sas=z3:sac=on:updr=off_300");
  fallback.push("lrs+1011_2_add=off:afr=on:afp=4000:afq=1.1:amm=off:bd=off:cond=fast:fde=none:gsp=on:gs=on:gsem=on:inw=on:ile=on:irw=on:nm=32:nwc=1:sas=z3:sos=on:sp=reverse_arity:tha=off:urr=ec_only:uhcvi=on_300");
  fallback.push("ott+1010_7_av=off:fsr=off:fde=none:lma=on:nm=2:newcnf=on:nwc=1.3:sos=on:sp=reverse_arity:uhcvi=on_300");
  fallback.push("ott+11_14_add=large:afp=1000:afq=1.4:amm=off:anc=none:fde=unused:gs=on:gsem=on:irw=on:nm=4:newcnf=on:nwc=1:sac=on:sp=occurrence_300");
  fallback.push("ott+11_5:4_aac=none:add=large:afp=4000:afq=1.4:amm=sco:anc=none:cond=fast:fde=none:gs=on:gsem=on:inw=on:ile=on:nm=2:newcnf=on:nwc=1:sas=z3:sos=on:sp=reverse_arity:urr=on:uhcvi=on_300");
  fallback.push("dis+10_3_afr=on:afp=1000:afq=1.0:anc=none:cond=on:fsr=off:gs=on:ile=on:irw=on:lwlo=on:nm=32:nwc=1:sos=all:sp=occurrence:urr=on_300");
  fallback.push("dis+10_14_add=large:afp=4000:afq=1.1:amm=sco:bs=unit_only:bsr=on:cond=fast:fde=none:inw=on:irw=on:lcm=predicate:nm=4:nwc=1.1:sos=on:sac=on:updr=off:uhcvi=on_300");
  fallback.push("lrs+10_8:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:anc=none:bs=unit_only:ccuc=first:cond=on:er=known:gs=on:gsaa=from_current:ile=on:lcm=reverse:nm=2:nwc=1.2:sac=on:urr=on:uhcvi=on_300");
  fallback.push("lrs+1002_8:1_add=off:afp=1000:afq=1.2:amm=sco:anc=none:bce=on:cond=on:ep=RS:gs=on:gsaa=from_current:ile=on:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off:uwa=interpreted_only:updr=off_300");
  fallback.push("lrs+1011_2:1_afr=on:afp=10000:afq=2.0:amm=off:gsp=on:gs=on:inw=on:ile=on:nm=2:nwc=1:sas=z3:tha=off_300");
  fallback.push("dis+1003_8_afr=on:anc=none:bd=preordered:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:sac=on:sp=reverse_arity:updr=off:uhcvi=on_300");
  fallback.push("lrs+1004_5:1_av=off:cond=on:fde=none:irw=on:lcm=reverse:lwlo=on:nm=64:newcnf=on:nwc=1:sos=on:sp=reverse_arity:updr=off:uhcvi=on_600");
  fallback.push("dis+10_4:1_add=off:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=occurrence:updr=off_300");
  fallback.push("ott-3_2:3_add=off:afr=on:afp=40000:afq=1.0:bsr=on:cond=fast:fsr=off:fde=none:gs=on:ile=on:lma=on:lwlo=on:nm=2:newcnf=on:nwc=1.2:nicw=on:sas=z3:sos=all:sp=reverse_arity:urr=ec_only:updr=off_300");
  fallback.push("lrs+1010_2:3_aac=none:acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bs=unit_only:bce=on:ccuc=first:fsr=off:fde=unused:gs=on:gsem=off:ile=on:nm=4:nwc=1:sos=on:sp=reverse_arity:uhcvi=on_300");
  fallback.push("dis+1002_5:4_add=off:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fsr=off:inw=on:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:tha=off:updr=off_300");
  fallback.push("lrs+10_8:1_aac=none:afr=on:afp=100000:afq=1.0:amm=off:cond=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1.7:sp=reverse_arity:urr=on:updr=off_300");
  fallback.push("lrs+11_1_afr=on:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:cond=on:gsp=on:gs=on:ile=on:irw=on:nm=6:nwc=1:sos=all:sac=on:urr=on_300");
  fallback.push("dis+1010_2:1_add=off:afp=10000:afq=2.0:anc=none:cond=on:fde=none:gs=on:gsaa=from_current:gsem=off:ile=on:irw=on:lma=on:lwlo=on:nm=2:nwc=1:sas=z3:sp=occurrence:uhcvi=on_300");
  fallback.push("dis+1011_5:1_afp=4000:afq=1.4:amm=off:anc=none:cond=on:fde=unused:gsp=on:ile=on:lma=on:nm=16:nwc=1:sos=on:sac=on:tha=off:urr=ec_only:uhcvi=on_300");
  fallback.push("lrs-4_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:cond=on:fde=unused:gs=on:gsem=off:inw=on:ile=on:irw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:sos=all:sp=occurrence:uwa=ground:urr=on:updr=off:uhcvi=on_300");
  fallback.push("ott+11_3:2_aac=none:add=large:afr=on:afp=1000:afq=1.4:amm=sco:anc=none:bs=on:bsr=on:br=off:cond=on:fsr=off:gsp=on:gs=on:irw=on:lcm=predicate:lma=on:nm=16:nwc=1.5:nicw=on:sas=z3:sac=on:sp=reverse_arity:tha=off:thi=all:urr=on:updr=off_1200");
  fallback.push("dis+1002_2_aac=none:add=off:afr=on:afp=100000:afq=1.2:amm=sco:anc=all:bsr=on:fde=unused:inw=on:ile=on:lcm=reverse:nm=4:nwc=4:nicw=on:sos=theory:sac=on:sp=reverse_arity:uhcvi=on_300");
  fallback.push("lrs+11_5:1_add=large:afr=on:afp=1000:afq=1.0:amm=off:anc=none:bd=off:gs=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:sac=on:sp=occurrence:tha=off:urr=ec_only_300");
  fallback.push("dis+11_4_afp=4000:afq=1.4:amm=sco:anc=none:gs=on:ile=on:lma=on:nm=64:nwc=1.7:sas=z3:sac=on:sp=occurrence_300");
  fallback.push("lrs-1_1_aac=none:add=off:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:gsp=on:gs=on:gsem=off:ile=on:lma=on:nm=64:nwc=1.5:sas=z3:urr=on_300");
  fallback.push("lrs+1011_3_add=off:afp=1000:afq=2.0:amm=off:anc=none:bsr=on:bce=on:cond=fast:fde=unused:ile=on:lma=on:nm=6:nwc=2:nicw=on:sas=z3:sd=3:ss=axioms:st=2.0:sp=reverse_arity:tha=off_300");
  fallback.push("lrs+11_4:1_add=large:afr=on:afp=40000:afq=2.0:amm=off:anc=none:cond=on:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sac=on:tha=off:urr=on:updr=off_300");
  fallback.push("lrs+11_5:1_add=off:afp=100000:afq=1.1:amm=off:anc=none:bd=off:cond=on:er=known:gs=on:gsem=off:inw=on:ile=on:irw=on:lcm=predicate:lwlo=on:nm=64:newcnf=on:nwc=1.1:sac=on:sp=reverse_arity:tha=off:thf=on_300");
  fallback.push("lrs+10_3:1_av=off:cond=on:fde=none:ile=on:lma=on:lwlo=on:nm=64:nwc=1:sp=reverse_arity:tar=off:uhcvi=on_300");
  fallback.push("dis+1_5:1_add=off:afp=40000:afq=1.2:anc=none:bd=off:cond=on:fsr=off:gs=on:ile=on:nm=64:nwc=4:sas=z3:updr=off_300");
  fallback.push("ott+10_6_add=off:afr=on:afp=1000:afq=1.0:amm=off:bsr=on:cond=on:fsr=off:fde=none:gs=on:gsem=on:ile=on:nm=2:newcnf=on:nwc=1:sp=reverse_arity:updr=off_300");
  fallback.push("lrs+11_5:1_add=off:afr=on:afp=4000:afq=1.1:anc=none:bsr=on:fsr=off:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:sac=on:sp=reverse_arity:urr=on:updr=off_300");
  fallback.push("dis+1011_8_afp=10000:afq=1.2:amm=sco:anc=none:bce=on:gs=on:gsem=off:ile=on:lma=on:nm=16:newcnf=on:nwc=2.5:sas=z3:sos=all:sac=on:sp=occurrence:updr=off_300");
  fallback.push("dis+1010_1_add=off:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:gs=on:gsem=off:inw=on:ile=on:irw=on:nm=6:nwc=1.3:nicw=on:sas=z3:tha=off:urr=ec_only_300");
  fallback.push("lrs+1011_8:1_add=off:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:fsr=off:gs=on:gsem=off:ile=on:irw=on:nm=2:nwc=1:sas=z3:sp=reverse_arity:tha=off:urr=on:updr=off_300");
  fallback.push("dis+11_3_add=off:afp=1000:afq=2.0:amm=off:anc=none:fsr=off:gs=on:gsaa=full_model:inw=on:ile=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:sos=all:sp=occurrence:tha=off:uhcvi=on_300");
  fallback.push("ott+11_1_add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:cond=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sp=occurrence:urr=ec_only_300");
  fallback.push("lrs+1010_1_add=off:afp=40000:afq=1.1:amm=off:anc=none:bd=off:fsr=off:inw=on:ile=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:sp=occurrence_300");
  fallback.push("ott+1011_3:1_add=off:afp=10000:afq=1.4:amm=off:anc=none:br=off:bce=on:cond=on:fde=unused:gs=on:ile=on:lma=on:nm=4:nwc=1:sp=occurrence:tar=off:urr=on:updr=off_300");
  fallback.push("dis+1003_2:1_afr=on:afp=100000:afq=1.1:anc=none:cond=on:fde=unused:ile=on:lma=on:newcnf=on:nwc=1:sp=occurrence:tar=off:uhcvi=on_300");
  fallback.push("ott+1011_3:2_av=off:bd=off:bs=on:bce=on:cond=on:fde=unused:ile=on:lma=on:newcnf=on:nwc=1:tha=off:updr=off_300");
  fallback.push("ott+2_4:1_aac=none:add=off:afp=10000:afq=1.1:amm=off:anc=none:bs=on:gs=on:gsem=off:ile=on:irw=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=reverse_arity_300");
  fallback.push("dis+1002_2_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:ep=RS:ile=on:nm=64:nwc=1:sac=on:sp=reverse_arity:uhcvi=on_300");
  fallback.push("lrs+1011_3_add=large:afr=on:afp=100000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sac=on:tar=off_300");
  fallback.push("lrs+1010_1_add=off:afp=1000:afq=1.0:amm=sco:anc=none:cond=on:fsr=off:gsp=on:gs=on:ile=on:lwlo=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=occurrence_300");
  fallback.push("dis+11_8_aac=none:add=large:afp=10000:afq=1.0:amm=sco:anc=none:bs=on:bsr=on:cond=on:er=known:fsr=off:fde=none:ile=on:lcm=predicate:lma=on:nm=32:nwc=1.7:nicw=on:sas=z3:sac=on:sp=occurrence:tha=off:updr=off_900");
  fallback.push("lrs+2_8:1_add=off:afp=40000:afq=1.0:anc=none:fde=unused:gs=on:ile=on:irw=on:lcm=reverse:nm=64:nwc=3:sas=z3:sp=occurrence:urr=on:uhcvi=on_300");
  fallback.push("lrs+10_5:1_afp=100000:afq=1.0:bd=preordered:inw=on:ile=on:irw=on:lcm=predicate:nm=6:nwc=1:sos=all:sp=reverse_arity:tha=off:uwa=interpreted_only:urr=on:updr=off:uhcvi=on_300");
  fallback.push("dis+1011_4:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bsr=on:fsr=off:ile=on:nm=64:nwc=5:sas=z3:sp=reverse_arity:urr=ec_only:updr=off_300");
  fallback.push("ott+1010_1_add=large:afp=1000:afq=1.2:anc=none:bd=off:ile=on:nm=2:newcnf=on:nwc=1:sp=occurrence:updr=off_300");
  fallback.push("ott+1011_3:1_add=off:afp=100000:afq=2.0:amm=off:anc=none:bs=unit_only:gs=on:gsem=on:irw=on:newcnf=on:nwc=1:sas=z3:tha=off_300");
  fallback.push("ott+1_8:1_add=large:afp=10000:afq=1.0:amm=sco:anc=none:bd=off:bsr=on:fsr=off:fde=unused:ile=on:irw=on:nm=0:newcnf=on:nwc=1:sas=z3:sp=occurrence:updr=off:uhcvi=on_300");
  fallback.push("dis+1010_2_acc=on:afr=on:afp=100000:afq=1.2:anc=none:bsr=on:fsr=off:ile=on:irw=on:nm=16:newcnf=on:nwc=4:sp=occurrence:tha=off:urr=ec_only_300");
  fallback.push("lrs+1002_2_add=large:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:inw=on:lwlo=on:nm=32:newcnf=on:nwc=1:sos=theory:sac=on:sp=occurrence:urr=on_300");
  fallback.push("ott+1_10_av=off:ep=RSTC:fsr=off:ile=on:lma=on:newcnf=on:nwc=1:sos=on:tha=off:updr=off_300");
  fallback.push("dis+1004_8_av=off:cond=on:er=filter:fde=unused:ile=on:lma=on:nm=64:newcnf=on:nwc=1:sp=reverse_arity_300");
  fallback.push("lrs+1010_2_anc=none:fsr=off:gs=on:irw=on:newcnf=on:nwc=1:sas=z3:sos=on:sp=occurrence:updr=off_300");
  fallback.push("lrs+1011_1_add=off:afr=on:afp=1000:afq=1.1:amm=off:anc=none:br=off:bce=on:er=filter:gsp=on:gs=on:gsaa=full_model:inw=on:ile=on:nm=32:nwc=1.2:sas=z3:uwa=one_side_constant:urr=on_300");
  fallback.push("lrs+11_6_av=off:bd=off:cond=fast:fde=none:lma=on:lwlo=on:nm=0:newcnf=on:nwc=1:sos=on:sp=reverse_arity:updr=off:uhcvi=on_300");
  fallback.push("dis+1010_4_afp=40000:afq=1.1:amm=sco:anc=none:cond=fast:fde=none:gs=on:gsem=on:ile=on:irw=on:nm=4:nwc=1:sp=reverse_arity:uhcvi=on_300");
  fallback.push("ott+1010_2:1_add=off:afr=on:afp=1000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:ile=on:nm=64:newcnf=on:nwc=1:sd=2:ss=axioms:st=1.5:sac=on:tha=off:updr=off_300");
  fallback.push("lrs+1011_3:2_av=off:bd=off:bsr=on:cond=on:fsr=off:gsp=on:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=64:nwc=1.5:sas=z3:sp=reverse_arity_300");
  fallback.push("lrs+10_2:1_add=off:afp=4000:afq=2.0:amm=sco:anc=none:bs=unit_only:br=off:cond=on:inw=on:ile=on:lma=on:nm=2:newcnf=on:nwc=1:sas=z3:urr=on:updr=off_300");
  fallback.push("lrs+4_6_av=off:bd=off:bs=unit_only:br=off:fsr=off:gsp=on:ile=on:irw=on:lcm=reverse:lma=on:nm=2:newcnf=on:nwc=1:sp=reverse_arity:urr=on:updr=off_300");
  fallback.push("dis+2_2_afr=on:afp=100000:afq=1.2:amm=off:anc=none:bsr=on:cond=on:gs=on:gsem=on:inw=on:ile=on:irw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=1.1:sas=z3:sac=on:tha=off:updr=off_300");
  fallback.push("lrs+1011_64_add=off:afr=on:afp=1000:afq=1.2:amm=off:anc=all_dependent:bsr=on:bce=on:cond=on:fsr=off:gs=on:inw=on:ile=on:nm=2:newcnf=on:nwc=1.1:sas=z3:sac=on:sp=occurrence:tha=off:thi=overlap:updr=off:uhcvi=on_300");
  fallback.push("lrs+2_4_add=large:afr=on:afp=100000:afq=1.1:amm=sco:anc=none:cond=on:ep=R:gs=on:gsaa=from_current:gsem=off:ile=on:lcm=reverse:lma=on:nm=2:nwc=1.1:sos=on:sac=on:tha=off:updr=off_300");
  fallback.push("dis+11_2_add=large:afp=1000:afq=1.1:anc=none:fsr=off:fde=none:ile=on:irw=on:lma=on:nm=64:nwc=1:sas=z3:sos=all:sac=on_300");
  fallback.push("ott+11_3_afr=on:afp=10000:afq=1.4:amm=off:anc=none:bsr=on:cond=on:er=known:ile=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1:sac=on_300");
  fallback.push("lrs+2_1024_av=off:bd=off:bsr=on:cond=fast:fsr=off:fde=none:ile=on:irw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:tha=off:thi=overlap:uwa=one_side_constant:updr=off:uhcvi=on_300");
  fallback.push("dis+1011_4_add=large:afr=on:afp=4000:afq=1.4:anc=none:cond=on:ep=RS:fsr=off:gs=on:gsaa=from_current:ile=on:lwlo=on:nm=64:nwc=1:sos=all:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_300");
  fallback.push("lrs+11_2:1_av=off:bd=off:br=off:bce=on:cond=on:fde=none:irw=on:lma=on:nm=2:newcnf=on:nwc=1.1:sp=occurrence:urr=on:updr=off:uhcvi=on_300");
  fallback.push("dis+11_4_add=off:afp=1000:afq=2.0:amm=sco:anc=none:fsr=off:gs=on:gsem=off:ile=on:nm=64:nwc=1.7:sas=z3:urr=on_300");
  fallback.push("dis+11_5_add=large:afr=on:afp=1000:afq=1.0:anc=none:bsr=on:fsr=off:nm=64:newcnf=on:nwc=1:updr=off_300");
  fallback.push("ott+1011_8:1_afr=on:afp=1000:afq=1.4:amm=sco:anc=none:bd=off:fsr=off:fde=unused:inw=on:ile=on:nm=2:nwc=1:nicw=on:sas=z3:sos=theory:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_600");
  fallback.push("lrs+1_4_add=off:afp=100000:afq=2.0:anc=none:bsr=on:br=off:cond=on:fde=unused:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=2:nwc=1:sas=z3:sos=on:sp=reverse_arity:urr=on:updr=off_300");
  fallback.push("dis+1011_1_afp=40000:afq=1.2:anc=none:cond=on:gsp=on:ile=on:irw=on:lma=on:newcnf=on:nwc=1:sac=on:sp=occurrence:tha=off:updr=off_300");
  fallback.push("lrs+1011_3_add=large:afp=10000:afq=1.1:amm=off:fde=unused:ile=on:irw=on:lma=on:nwc=1.7:sp=reverse_arity:tha=off:thf=on:updr=off_300");
  fallback.push("dis+1011_12_afp=100000:afq=1.0:amm=sco:anc=none:fsr=off:fde=unused:gsp=on:ile=on:irw=on:nm=64:nwc=1.2:sac=on:sp=occurrence:tac=axiom:tar=off:uhcvi=on_300");
  fallback.push("lrs+1011_2:1_av=off:fsr=off:gs=on:gsem=off:inw=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1:sp=occurrence:tha=off:urr=ec_only:uhcvi=on_300");
  fallback.push("dis+1011_8:1_add=off:afp=10000:afq=1.0:amm=off:anc=none:bd=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sac=on:sp=reverse_arity:updr=off_300");
  fallback.push("dis+1011_4_afr=on:afp=4000:afq=1.4:anc=none:fsr=off:gs=on:gsem=on:ile=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:tha=off:updr=off_300");
  fallback.push("lrs-11_2:1_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:inw=on:ile=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.5:sas=z3:sp=reverse_arity:urr=on_300");
  fallback.push("dis+1002_5_add=large:afr=on:afp=4000:afq=1.4:amm=off:anc=none:fsr=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sos=all:sac=on:sp=occurrence:updr=off_300");
  fallback.push("lrs+1003_3:2_afp=1000:afq=2.0:amm=off:anc=none:cond=on:gs=on:ile=on:lma=on:nm=6:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off:thi=all:updr=off_300");
  fallback.push("dis+10_32_add=large:afp=40000:afq=1.0:anc=none:bd=off:bsr=on:fde=none:lma=on:nm=0:newcnf=on:nwc=1:nicw=on:sp=occurrence:tha=off:thi=full:uhcvi=on_300");
  fallback.push("dis+11_8:1_afp=100000:afq=1.4:amm=sco:anc=none:cond=fast:fde=none:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=64:nwc=1:sos=all:sac=on:urr=on:uhcvi=on_300");
  fallback.push("lrs+11_1_add=off:afp=100000:afq=1.4:amm=off:anc=none:bsr=on:fsr=off:gs=on:ile=on:nm=64:nwc=1:sas=z3:sac=on:sp=occurrence:updr=off_300");
  fallback.push("ott+11_8:1_acc=model:add=off:afr=on:afp=100000:afq=2.0:amm=off:anc=none:ccuc=first:cond=on:fde=none:gs=on:gsaa=from_current:gsem=on:ile=on:lwlo=on:nm=2:nwc=1:sos=all:urr=on_300");
  fallback.push("lrs-2_5:1_acc=on:add=off:afr=on:afp=40000:afq=1.1:amm=off:anc=none:bd=off:cond=fast:gs=on:ile=on:nm=0:newcnf=on:nwc=3:sac=on:thf=on:urr=ec_only_300");
  fallback.push("fmb+10_1_av=off:bce=on:fmbsr=1.3:fde=none:nm=64:newcnf=on_900");
  fallback.push("lrs+11_3_afr=on:afp=40000:afq=1.1:anc=none:fsr=off:gs=on:gsem=off:inw=on:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:sos=all:sac=on:sp=occurrence:updr=off_300");
  fallback.push("ott-4_5:4_aac=none:afr=on:afp=100000:afq=1.2:amm=sco:anc=none:bd=off:bsr=on:br=off:cond=fast:ile=on:irw=on:lcm=reverse:lma=on:nm=64:newcnf=on:nwc=3:thf=on:urr=on:updr=off:uhcvi=on_300");
  fallback.push("lrs+11_5:1_afr=on:afp=10000:afq=1.2:amm=off:anc=none:fsr=off:gs=on:inw=on:ile=on:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:sac=on:sp=occurrence:tha=off_300");
  fallback.push("lrs+1002_5_av=off:cond=fast:fsr=off:fde=unused:gs=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1.7:sp=reverse_arity_300");
  fallback.push("lrs+1010_1_afp=1000:afq=1.4:amm=off:anc=none:bd=off:bsr=on:br=off:cond=on:ile=on:irw=on:nm=2:nwc=1:nicw=on:sas=z3:sos=all:sp=reverse_arity:tha=off:urr=on:updr=off_300");
  fallback.push("lrs+10_8_afr=on:afp=4000:afq=1.1:amm=sco:anc=none:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:sac=on:tha=off:urr=on:updr=off_300");
  fallback.push("lrs+11_1_av=off:bd=off:bsr=on:cond=on:fsr=off:ile=on:nm=64:newcnf=on:nwc=1:tha=off:updr=off_300");
  fallback.push("lrs+1011_2:1_aac=none:add=off:afp=1000:afq=1.0:amm=off:bs=on:gs=on:gsaa=from_current:gsem=on:ile=on:lcm=reverse:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sp=reverse_arity:tha=off_300");
  fallback.push("lrs+10_2:3_afr=on:afp=1000:afq=1.1:bd=off:bce=on:cond=on:gsp=on:gs=on:gsaa=from_current:inw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:sp=reverse_arity:tha=off:uwa=interpreted_only:updr=off:uhcvi=on_300");
  fallback.push("dis+11_10_add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:cond=on:gs=on:gsem=on:inw=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=10:sas=z3:sac=on:sp=reverse_arity_300");
  fallback.push("ott+11_4_av=off:ile=on:lma=on:nm=64:nwc=1:sos=all:sp=occurrence:uwa=interpreted_only:updr=off:uhcvi=on_300");
  fallback.push("dis+11_3:1_av=off:br=off:ep=R:fsr=off:gsp=on:ile=on:lma=on:nm=2:newcnf=on:nwc=1:sas=z3:sp=reverse_arity:urr=on:uhcvi=on_300");
  fallback.push("dis+10_2_add=off:amm=off:anc=none:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:ile=on:irw=on:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off:updr=off:uhcvi=on_300");
  fallback.push("lrs+1011_1_add=large:afr=on:afp=1000:afq=1.4:anc=none:bd=off:cond=on:ile=on:irw=on:nm=2:nwc=1.7:tha=off_300");
  fallback.push("lrs+11_2:1_add=off:anc=none:bsr=on:br=off:cond=on:er=filter:fsr=off:gs=on:gsem=on:inw=on:ile=on:lma=on:nm=2:nwc=1:sas=z3:sos=all:sac=on:uwa=ground:urr=on_300");
  fallback.push("dis+1004_16_av=off:fsr=off:fde=unused:ile=on:irw=on:nm=0:newcnf=on:nwc=1.1:sp=reverse_arity:urr=on_300");
  fallback.push("lrs+11_4:1_av=off:bd=off:bs=unit_only:cond=on:fsr=off:fde=none:ile=on:irw=on:lwlo=on:nm=4:nwc=1.1:sp=reverse_arity_300");
  fallback.push("dis-1_128_av=off:bs=on:fde=unused:ile=on:irw=on:nm=32:nwc=1.1:sos=all:tha=off:thi=full:uwa=one_side_constant:uhcvi=on_600");
  fallback.push("dis+10_3_add=large:afp=4000:afq=1.4:amm=off:anc=none:cond=on:ep=RS:gs=on:gsaa=from_current:inw=on:ile=on:lma=on:nm=2:newcnf=on:nwc=1:sac=on:tha=off:updr=off_300");
  fallback.push("lrs+11_2_av=off:br=off:ep=R:ile=on:lma=on:nm=64:nwc=1:urr=on_300");
  fallback.push("lrs-1_3:1_av=off:bd=off:cond=on:gs=on:ile=on:lcm=reverse:lma=on:nm=32:nwc=1.2:urr=on:updr=off_300");
  fallback.push("ott+1011_5:4_aac=none:add=large:afp=100000:afq=2.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:cond=on:gs=on:inw=on:ile=on:irw=on:lma=on:nm=32:nwc=1:nicw=on:sas=z3:sos=on:sp=occurrence:tha=off:updr=off:uhcvi=on_300");
  fallback.push("lrs+1010_1_add=large:afr=on:afp=40000:afq=2.0:anc=none:br=off:fsr=off:inw=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sos=all:urr=on_300");
  fallback.push("lrs-11_5:4_afp=4000:afq=1.4:amm=sco:anc=none:bd=off:br=off:gs=on:gsem=off:inw=on:nm=64:newcnf=on:nwc=1:sas=z3:sos=all:sp=occurrence:urr=on_300");
  fallback.push("lrs+10_24_afp=4000:afq=2.0:bd=off:bsr=on:bce=on:cond=fast:fsr=off:gsp=on:gs=on:gsem=on:inw=on:ile=on:nwc=1.3:sp=occurrence:tha=off:uwa=one_side_constant:urr=ec_only_300");
  fallback.push("ott+1004_3_av=off:fde=none:gs=on:gsem=on:ile=on:nm=0:nwc=1.3:sp=reverse_arity:tha=off:thi=overlap:urr=ec_only:updr=off_300");
  fallback.push("lrs+10_24_av=off:bd=off:cond=on:gs=on:gsem=off:inw=on:ile=on:irw=on:nm=64:nwc=2.5:sp=occurrence_300");
  fallback.push("lrs+11_5:1_afr=on:afp=100000:afq=1.4:anc=none:cond=fast:fsr=off:ile=on:irw=on:nm=64:nwc=5:nicw=on:sas=z3:sp=reverse_arity:tha=off:thi=all:uwa=one_side_interpreted:updr=off_600");
  fallback.push("lrs+11_2_add=large:afr=on:amm=sco:anc=none:bsr=on:gs=on:gsem=off:irw=on:lma=on:nm=16:newcnf=on:nwc=1:sac=on:sp=occurrence:urr=on:updr=off_300");
  fallback.push("dis+1010_2_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:bd=off:fsr=off:fde=none:ile=on:lcm=reverse:lma=on:nm=64:nwc=1:nicw=on:sas=z3:sp=reverse_arity_300");
  fallback.push("lrs-10_3_av=off:bs=unit_only:bsr=on:cond=on:fsr=off:fde=unused:gs=on:inw=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.2:sas=z3:tha=off:urr=ec_only_300");
  fallback.push("dis-10_3_aac=none:acc=model:add=off:afp=100000:afq=1.1:anc=none:bs=unit_only:bce=on:ccuc=small_ones:cond=on:fsr=off:fde=none:gsp=on:ile=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=2:nwc=1.5:sos=on:sp=occurrence:uwa=ground:urr=ec_only:uhcvi=on_300");
  fallback.push("dis-11_4:1_aac=none:add=large:afp=4000:afq=1.2:anc=none:fsr=off:ile=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1:sas=z3:sp=occurrence_300");
  fallback.push("lrs+1_5:1_add=off:afr=on:afp=40000:afq=2.0:amm=off:anc=none:cond=on:gs=on:gsem=off:ile=on:lma=on:nm=64:nwc=1.2:sp=reverse_arity_300");
  fallback.push("lrs+1002_3_av=off:bs=unit_only:bsr=on:ile=on:nm=64:nwc=1:sos=theory:sp=reverse_arity_300");
  fallback.push("dis+1011_8_av=off:bd=off:bs=unit_only:bsr=on:cond=on:irw=on:nm=64:newcnf=on:nwc=1_300");
  fallback.push("lrs+10_2:1_add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bs=unit_only:cond=fast:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:ile=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sac=on:tac=axiom:tar=off:tha=off:uwa=ground:uhcvi=on_300");
  fallback.push("lrs-1_128_aac=none:add=off:afp=40000:afq=1.0:amm=off:anc=none:fsr=off:inw=on:ile=on:lcm=reverse:lma=on:nm=16:nwc=10:sas=z3:sac=on:updr=off_300");
  fallback.push("dis+1010_1_av=off:lma=on:newcnf=on:nwc=1:sd=4:ss=axioms:sos=on:sp=reverse_arity_300");
  fallback.push("dis+1004_1_add=off:afr=on:afp=1000:afq=1.1:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=from_current:gsem=on:ile=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=occurrence:tac=light:tar=off:tha=off:thi=all:urr=on:uhcvi=on_300");
  fallback.push("lrs+11_8:1_add=large:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=fast:gs=on:gsaa=full_model:inw=on:ile=on:lcm=predicate:nm=4:newcnf=on:nwc=1:sp=reverse_arity:tha=off:urr=on_300");
  fallback.push("dis+10_3_add=off:afp=100000:afq=1.4:amm=sco:anc=none:fsr=off:gs=on:gsem=on:inw=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sp=reverse_arity:tha=off:thf=on:updr=off_300");
  fallback.push("dis+1011_3_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fde=none:gs=on:gsem=off:ile=on:lma=on:lwlo=on:nm=4:nwc=1:sac=on:tha=off:updr=off:uhcvi=on_300");
  fallback.push("dis+1011_1_av=off:fsr=off:fde=unused:gsp=on:ile=on:irw=on:lma=on:nwc=1:sos=on:sp=reverse_arity:urr=ec_only_300");
  fallback.push("lrs+11_5:4_av=off:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=32:newcnf=on:nwc=1.3:sp=reverse_arity:updr=off_300");
  fallback.push("dis+11_5_add=large:afr=on:afp=10000:afq=1.2:anc=none:gs=on:gsem=on:ile=on:irw=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:sp=reverse_arity:urr=on:updr=off_300");
  fallback.push("dis+1011_8:1_av=off:ile=on:lma=on:nm=32:newcnf=on:nwc=1:sp=occurrence_300");
  fallback.push("dis+1010_5_av=off:bsr=on:cond=fast:fde=unused:ile=on:nm=6:nwc=1:uhcvi=on_600");
  fallback.push("ott+1_1_av=off:bsr=on:cond=on:fsr=off:gsp=on:gs=on:gsem=off:ile=on:lma=on:nm=4:newcnf=on:nwc=1:sp=occurrence:urr=on_600");
  fallback.push("ott+1003_5_av=off:bd=off:bs=on:er=known:fde=none:gs=on:gsem=off:ile=on:nwc=2.5:sos=all:sp=occurrence:urr=on_300");
  fallback.push("lrs-11_4:1_afp=100000:afq=1.2:amm=off:anc=all_dependent:bs=unit_only:fsr=off:fde=none:gs=on:gsem=on:ile=on:lma=on:nm=64:nwc=1:sp=reverse_arity:updr=off:uhcvi=on_300");
  fallback.push("dis+11_7_add=large:afr=on:afp=10000:afq=1.2:bd=off:bsr=on:cond=on:fsr=off:fde=unused:gs=on:ile=on:lcm=predicate:lma=on:nm=2:newcnf=on:nwc=3:sos=on:sp=reverse_arity:tha=off:updr=off_300");
  fallback.push("lrs+1011_10_av=off:cond=fast:er=filter:fsr=off:fde=none:gs=on:gsem=on:ile=on:lma=on:nm=4:nwc=1:sos=all:sp=reverse_arity:tha=off:thi=new:uwa=ground:updr=off:uhcvi=on_300");
  fallback.push("lrs+1010_20_add=large:afr=on:afp=4000:afq=1.4:amm=sco:anc=none:bd=preordered:bs=unit_only:fsr=off:fde=unused:gs=on:ile=on:lcm=reverse:nm=2:nwc=4:sas=z3:sac=on:sp=occurrence:tha=off:urr=on:updr=off:uhcvi=on_1200");
  fallback.push("dis+11_3_add=large:afp=100000:afq=1.4:amm=off:anc=none:fsr=off:gs=on:ile=on:irw=on:lma=on:nm=32:nwc=1:tha=off:updr=off_300");
  fallback.push("lrs+1011_8_aac=none:acc=model:add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:ccuc=first:cond=on:fde=none:gs=on:gsaa=from_current:inw=on:ile=on:nm=2:nwc=1:sos=on:sp=reverse_arity:tha=off:urr=on_300");
  fallback.push("dis+11_3_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bce=on:cond=on:fsr=off:ile=on:lwlo=on:nm=64:newcnf=on:nwc=1:sas=z3:tha=off:thf=on_300");
  fallback.push("lrs+4_8:1_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:ile=on:irw=on:lcm=reverse:lma=on:nm=2:nwc=1:sos=all:tha=off_300");
  fallback.push("lrs+1003_8:1_av=off:fsr=off:fde=unused:gsp=on:gs=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sos=on_300");
  fallback.push("lrs+11_10_add=off:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:bce=on:cond=fast:gsp=on:inw=on:lma=on:nm=4:newcnf=on:nwc=1:sp=occurrence:tha=off:thf=on:urr=ec_only:uhcvi=on_300");
  fallback.push("dis+1010_3_afp=10000:afq=2.0:amm=off:anc=none:cond=on:fsr=off:gs=on:gsem=off:inw=on:ile=on:irw=on:nm=64:nwc=1:sas=z3:tha=off:urr=on_300");
  fallback.push("ott+1003_12_add=large:anc=all:bd=preordered:bce=on:fde=none:lcm=reverse:lma=on:nm=0:newcnf=on:nwc=1:nicw=on:sac=on:sp=reverse_arity:tha=off:uwa=ground_600");
  fallback.push("dis-3_7_av=off:bs=unit_only:bsr=on:cond=on:fsr=off:fde=none:gsp=on:ile=on:irw=on:lma=on:nm=4:nwc=1:sos=all:sp=occurrence:tha=off:thi=overlap:uwa=interpreted_only:uhcvi=on_300");
  fallback.push("lrs+11_5_av=off:cond=on:lma=on:nm=64:newcnf=on:nwc=1:updr=off_300");
  fallback.push("lrs+1011_7_av=off:cond=on:gs=on:ile=on:nm=64:nwc=3:updr=off_300");
  fallback.push("ott-1_24_av=off:bd=off:cond=fast:er=known:fsr=off:fde=unused:gsp=on:irw=on:lma=on:lwlo=on:nm=0:newcnf=on:nwc=1.3:sp=occurrence:tha=off:thi=new:uhcvi=on_300");
  fallback.push("dis+1011_2:3_add=large:afr=on:afp=40000:afq=1.0:anc=none:br=off:cond=on:gs=on:gsem=on:ile=on:irw=on:lma=on:lwlo=on:nwc=1:sos=on:sac=on:sp=occurrence:tac=axiom:tar=off:urr=on:updr=off_300");
  fallback.push("lrs+1002_1_add=off:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:fsr=off:gsp=on:inw=on:ile=on:lcm=predicate:lwlo=on:nm=64:nwc=1.7:sas=z3:sac=on:sp=reverse_arity:tha=off:thf=on_300");
  fallback.push("fmb+10_1_av=off:fmbes=contour:fmbsr=1.3:ile=on:nm=2:newcnf=on:updr=off_300");
  fallback.push("lrs+1010_8:1_av=off:br=off:cond=on:fsr=off:gsp=on:gs=on:gsem=off:inw=on:ile=on:irw=on:lma=on:nm=4:nwc=5:sos=on:tha=off:thf=on:urr=on_300");
  fallback.push("lrs+1002_3_afr=on:afp=40000:afq=2.0:anc=none:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:inw=on:ile=on:irw=on:lma=on:nm=2:nwc=1.1:nicw=on:sas=z3:sac=on:updr=off:uhcvi=on_300");
  fallback.push("dis+10_2:1_aac=none:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:cond=on:fsr=off:gs=on:gsem=on:inw=on:ile=on:irw=on:nm=2:nwc=1.1:nicw=on:sas=z3:sos=theory:urr=on:updr=off_300");
  fallback.push("lrs+11_8:1_av=off:cond=on:fde=none:ile=on:nm=16:nwc=1.3:sp=reverse_arity:urr=on:updr=off_300");
  fallback.push("lrs+1002_3_acc=on:amm=sco:anc=none:ccuc=small_ones:gs=on:gsem=on:ile=on:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:urr=on_300");
  fallback.push("lrs+1011_12_afr=on:afp=100000:afq=1.4:amm=off:anc=none:cond=on:fsr=off:gs=on:ile=on:nm=64:nwc=1:sas=z3:sac=on:tha=off:thf=on:urr=on_300");
  fallback.push("lrs+2_8_av=off:bsr=on:cond=on:fsr=off:ile=on:lma=on:nm=64:nwc=1.2:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_300");
  fallback.push("dis+1_8:1_av=off:br=off:fsr=off:fde=none:gsp=on:ile=on:lma=on:nm=2:nwc=1:sos=on:sp=reverse_arity:urr=on:updr=off_300");
  fallback.push("dis+1011_3:2_afp=1000:afq=1.2:anc=none:bd=off:fde=none:gsp=on:gs=on:gsaa=from_current:gsem=off:ile=on:irw=on:lma=on:lwlo=on:nm=6:nwc=1:nicw=on:sas=z3:sos=on:sac=on:sp=reverse_arity:urr=ec_only_300");
  fallback.push("lrs+1010_24_afp=40000:afq=2.0:amm=off:anc=none:cond=fast:gs=on:gsem=off:inw=on:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:tha=off:thf=on:updr=off:uhcvi=on_300");
  fallback.push("dis+10_1_add=off:afp=4000:afq=1.4:amm=sco:anc=none:cond=on:ep=RSTC:gs=on:gsem=on:ile=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sos=on:sac=on:sp=reverse_arity_300");
  fallback.push("lrs+1004_2_av=off:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lwlo=on:nm=0:nwc=1:sp=occurrence:tha=off:thi=new:updr=off:uhcvi=on_300");
  fallback.push("dis+1004_4:1_av=off:br=off:cond=on:ep=RST:fsr=off:ile=on:lma=on:nm=2:newcnf=on:nwc=1.1:sp=occurrence:urr=on_300");
  fallback.push("lrs+11_2_av=off:cond=on:fsr=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sp=reverse_arity:tha=off:thf=on_300");
  fallback.push("ott+1011_2:3_av=off:bs=unit_only:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:nm=2:newcnf=on:nwc=1:sp=reverse_arity:tha=off:thi=all:uwa=all:urr=on:uhcvi=on_300");
  fallback.push("lrs+10_3_av=off:bs=unit_only:bce=on:cond=on:fde=unused:gsp=on:gs=on:inw=on:irw=on:nm=0:newcnf=on:nwc=1.1:tha=off:uhcvi=on_300");
  fallback.push("dis+1011_10_av=off:bd=off:cond=fast:er=known:inw=on:ile=on:irw=on:lma=on:nwc=1.7:sp=occurrence:tha=off:uhcvi=on_300");
  fallback.push("lrs+10_14_add=large:afp=40000:afq=1.1:amm=sco:fde=unused:gs=on:gsem=on:ile=on:lma=on:nm=6:newcnf=on:nwc=1:nicw=on:sp=reverse_arity:tha=off:uwa=one_side_interpreted:updr=off:uhcvi=on_300");
  fallback.push("ott+1011_2:3_add=large:afr=on:afp=40000:afq=2.0:anc=none:br=off:bce=on:cond=fast:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:newcnf=on:nwc=1.1:sp=reverse_arity:tha=off:urr=on:updr=off_300");
  fallback.push("dis+2_3_add=off:afp=40000:afq=1.1:anc=none:cond=on:gs=on:inw=on:ile=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:sp=reverse_arity:tha=off:urr=on:updr=off_300");
  fallback.push("lrs+1011_2:1_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:bd=preordered:ccuc=first:cond=fast:fsr=off:fde=unused:inw=on:ile=on:irw=on:lma=on:nm=64:nwc=2:nicw=on:sp=occurrence:urr=ec_only:updr=off_300");
  fallback.push("ott+1011_5_av=off:fde=unused:gsp=on:gs=on:gsem=off:ile=on:nm=32:nwc=1.3:sas=z3:sp=reverse_arity:tha=off:uwa=ground_300");
  fallback.push("lrs+10_50_av=off:cond=fast:fde=none:lcm=reverse:nm=64:newcnf=on:nwc=1:sp=occurrence:tha=off:uhcvi=on_300");
  fallback.push("dis+1011_3:1_add=off:afr=on:afp=40000:afq=1.1:amm=sco:bd=off:bce=on:cond=fast:gsp=on:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=4:nwc=1.5:sas=z3:sos=all:sp=occurrence:tha=off:uwa=interpreted_only:uhcvi=on_300");
  fallback.push("dis+10_3:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:bd=off:cond=on:ile=on:nm=2:nwc=2.5:sas=z3:sac=on:sp=occurrence_300");
  fallback.push("lrs+1003_3:1_av=off:bsr=on:cond=fast:fde=unused:inw=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1:sos=all:sp=occurrence:tha=off:updr=off:uhcvi=on_300");
  fallback.push("ott+10_4:1_afp=100000:afq=1.1:anc=none:bd=off:inw=on:ile=on:irw=on:lma=on:nm=4:nwc=1:sos=all:sac=on:sp=occurrence:tha=off:urr=on:updr=off_300");
  fallback.push("dis+11_3_av=off:cond=on:fsr=off:ile=on:irw=on:nm=64:newcnf=on:nwc=1:sp=reverse_arity:tha=off:updr=off:uhcvi=on_300");
  fallback.push("lrs+4_4_av=off:bd=off:bs=unit_only:cond=fast:fsr=off:fde=unused:gs=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1:sp=occurrence:tha=off:thf=on:updr=off_300");
  fallback.push("dis+11_32_add=large:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:er=filter:ile=on:lcm=predicate:lma=on:newcnf=on:nwc=5:sp=occurrence:updr=off_300");
  fallback.push("lrs+2_4_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bd=off:bce=on:fde=none:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:tha=off:thi=strong:uwa=one_side_interpreted:urr=on:updr=off:uhcvi=on_300");
  fallback.push("dis+1010_1_av=off:ile=on:irw=on:nm=2:nwc=1:sas=z3:sp=occurrence:tar=off:urr=on_300");
  fallback.push("lrs+1010_1_av=off:fde=unused:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sos=all:sp=reverse_arity:updr=off_300");
  fallback.push("lrs+10_3:2_av=off:bce=on:cond=on:er=filter:fsr=off:fde=unused:gs=on:gsem=on:ile=on:irw=on:nm=6:nwc=1:sos=all:tac=light:tar=off:updr=off:uhcvi=on_300");
  fallback.push("lrs+11_7_add=off:afr=on:afp=40000:afq=1.1:amm=off:anc=none:bsr=on:br=off:fde=unused:gs=on:gsem=on:inw=on:ile=on:irw=on:lma=on:nm=64:nwc=1:sos=all:sac=on:urr=on:updr=off:uhcvi=on_300");
  fallback.push("lrs+10_24_add=off:afp=100000:afq=1.2:amm=sco:anc=none:cond=on:fsr=off:gs=on:ile=on:nm=64:nwc=1:sp=occurrence:tha=off:thf=on_300");
  fallback.push("lrs-2_3:1_add=off:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:cond=on:er=filter:fde=unused:ile=on:irw=on:nm=64:newcnf=on:nwc=1.1:sas=z3:sac=on:sp=reverse_arity:tha=off:thf=on:thi=strong:uhcvi=on_600");
  fallback.push("dis+11_5:4_aac=none:acc=on:afp=40000:afq=2.0:amm=sco:anc=none:bd=off:cond=fast:fsr=off:fde=none:lcm=reverse:nm=2:newcnf=on:nwc=1.1:tha=off:thi=strong:uwa=interpreted_only:uhcvi=on_300");
  fallback.push("lrs+2_3:2_av=off:cond=fast:inw=on:ile=on:nm=2:nwc=1:sos=theory:urr=on_300");
  fallback.push("lrs+1011_5_add=large:afp=1000:afq=1.2:amm=off:anc=none:br=off:fsr=off:gs=on:gsem=on:inw=on:ile=on:lma=on:nm=32:nwc=1:sas=z3:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_300");
  fallback.push("dis+1011_5:1_afr=on:afp=10000:afq=1.2:amm=sco:bd=preordered:bs=unit_only:cond=on:fsr=off:inw=on:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=1.1:sd=7:ss=axioms:st=1.2:tha=off:uhcvi=on_300");
  fallback.push("ott+4_4_av=off:bd=off:er=filter:ile=on:irw=on:lma=on:nm=64:nwc=1:sos=on:sp=reverse_arity:updr=off_300");
  fallback.push("fmb+10_1_av=off:bce=on:fmbes=contour:fmbsr=2.0:ile=on:nm=2_600");
  fallback.push("ott+2_6_add=large:afr=on:afp=4000:afq=2.0:amm=sco:anc=all:bs=on:bce=on:cond=fast:fde=none:gs=on:gsem=off:ile=on:nm=64:newcnf=on:nwc=1:sac=on:urr=on:updr=off_300");
  fallback.push("dis+10_4:1_afp=10000:afq=1.4:anc=none:bd=off:fsr=off:gsp=on:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=reverse_arity:urr=on:updr=off_300");
  fallback.push("lrs+11_8_afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=off:inw=on:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:tha=off:urr=ec_only:updr=off_300");
  fallback.push("lrs+10_5:4_av=off:bd=off:fsr=off:fde=none:lcm=reverse:lma=on:newcnf=on:nwc=1:tha=off:urr=on:updr=off_300");
  fallback.push("lrs+1011_5:4_aac=none:add=off:afr=on:afp=1000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:bsr=on:cond=on:fde=none:gsp=on:gs=on:gsaa=from_current:gsem=on:inw=on:ile=on:nm=16:nwc=1:sas=z3:sos=on:sp=reverse_arity:tha=off:uwa=interpreted_only:uhcvi=on_300");
  fallback.push("dis+1_4:1_acc=on:add=large:afp=4000:afq=1.2:amm=sco:anc=none:ccuc=small_ones:ile=on:lwlo=on:nm=64:nwc=1:tha=off:urr=ec_only:updr=off_300");
  fallback.push("lrs+10_2:1_av=off:cond=on:fde=none:gs=on:gsem=off:ile=on:irw=on:nm=64:nwc=1:sp=occurrence:urr=on_300");
  fallback.push("ott+11_5:4_aac=none:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:bce=on:cond=on:fsr=off:fde=unused:ile=on:irw=on:lma=on:nm=6:newcnf=on:nwc=1:nicw=on:sas=z3:tha=off:updr=off_300");
  fallback.push("dis+11_3_afr=on:afp=40000:afq=2.0:anc=none:fsr=off:gs=on:lma=on:nm=64:newcnf=on:nwc=1:nicw=on:sas=z3:sos=all:sac=on:sp=occurrence:urr=on_300");
  fallback.push("lrs+1002_2:1_aac=none:add=large:afr=on:afp=40000:afq=1.1:amm=off:anc=none:cond=fast:gs=on:nm=64:newcnf=on:nwc=1.5:sas=z3:sp=occurrence:updr=off_300");
  fallback.push("lrs-11_5_add=off:afr=on:afp=100000:afq=1.0:anc=all:bs=unit_only:cond=fast:fsr=off:ile=on:irw=on:lcm=reverse:lwlo=on:nwc=1.7:nicw=on:sos=on:sac=on:sp=reverse_arity:tha=off:urr=on_300");
  fallback.push("dis+1003_4:1_add=large:afp=10000:afq=1.4:amm=off:anc=none:bd=off:cond=fast:fsr=off:fde=none:gs=on:ile=on:lma=on:nm=64:nwc=1.2:sas=z3:sp=reverse_arity:tha=off:urr=ec_only_300");
  fallback.push("lrs+1002_1_av=off:bd=off:bsr=on:cond=on:ile=on:lma=on:nm=64:nwc=1:sos=on:sp=reverse_arity_300");
  fallback.push("lrs+1010_8:1_add=off:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:gsp=on:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=64:nwc=2:updr=off_300");
  fallback.push("dis+1004_3_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:bs=unit_only:bsr=on:bce=on:ile=on:nm=64:newcnf=on:nwc=1:nicw=on:urr=ec_only_300");
  fallback.push("ott-10_4_av=off:bd=preordered:fsr=off:fde=none:ile=on:irw=on:nm=2:newcnf=on:nwc=1:updr=off:uhcvi=on_600");
  fallback.push("lrs+11_8:1_afp=100000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:cond=on:fsr=off:gs=on:gsem=off:ile=on:irw=on:lcm=reverse:nm=64:nwc=2:nicw=on:sac=on:sp=occurrence:urr=on:updr=off_300");
  fallback.push("dis+1003_28_acc=model:add=large:afp=10000:afq=1.1:amm=off:anc=none:bd=off:ccuc=first:fsr=off:gs=on:gsaa=from_current:ile=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence:tha=off:uwa=ground:uhcvi=on_300");
  fallback.push("lrs+1002_1_aac=none:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ile=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1:sac=on:sp=occurrence:tha=off:updr=off_300");
  fallback.push("dis+1002_14_av=off:cond=fast:fde=unused:inw=on:ile=on:lma=on:nm=0:nwc=1:sos=all:sp=reverse_arity:tha=off:uwa=one_side_interpreted:uhcvi=on_300");
  fallback.push("lrs+1_3:2_aac=none:afr=on:afp=40000:afq=1.0:anc=none:bs=unit_only:lma=on:nm=64:newcnf=on:nwc=3:sas=z3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_300");
  fallback.push("lrs+1010_3:1_av=off:bd=off:bsr=on:irw=on:nm=64:newcnf=on:nwc=1.7:sos=all:updr=off_300");
  fallback.push("lrs-11_8:1_afr=on:afp=1000:afq=1.4:amm=off:anc=none:bd=off:bs=on:gs=on:ile=on:lcm=predicate:lma=on:nm=64:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off:thi=strong:uwa=interpreted_only_300");
  fallback.push("dis-4_4_add=large:afp=1000:afq=1.4:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=off:ile=on:irw=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:sp=reverse_arity:updr=off:uhcvi=on_300");
  fallback.push("ott+1002_2:1_add=large:afr=on:afp=100000:afq=1.1:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=from_current:irw=on:lcm=reverse:nm=64:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off:updr=off_300");
  fallback.push("lrs-11_4_acc=on:afr=on:afp=40000:afq=1.4:amm=off:anc=none:br=off:bce=on:cond=fast:fde=none:gs=on:ile=on:irw=on:nm=0:newcnf=on:nwc=1.1:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off_300");
  fallback.push("dis+1010_1_afr=on:afp=40000:afq=2.0:amm=off:anc=none:gs=on:ile=on:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off_300");
  fallback.push("lrs+1010_5:4_afp=100000:afq=1.2:anc=none:cond=on:fsr=off:ile=on:irw=on:nm=64:nwc=1:sac=on:sp=occurrence:urr=on_300");
  fallback.push("ott+1_5:1_av=off:bs=unit_only:br=off:gs=on:gsem=off:inw=on:ile=on:nm=64:newcnf=on:nwc=1:sd=4:ss=axioms:st=1.5:sp=occurrence:tha=off:urr=on:uhcvi=on_300");
  fallback.push("dis+1002_1_add=large:afp=4000:afq=1.2:anc=none:cond=on:fsr=off:gs=on:gsem=off:ile=on:lma=on:nm=64:nwc=1:sas=z3:sac=on:sp=occurrence:tha=off:thi=strong:uwa=interpreted_only:uhcvi=on_300");
  fallback.push("dis+11_5_av=off:cond=on:fsr=off:ile=on:lwlo=on:nm=64:nwc=3:sp=reverse_arity:updr=off_300");
  fallback.push("lrs+1011_2:3_av=off:bsr=on:cond=fast:fsr=off:gsp=on:ile=on:irw=on:lwlo=on:nm=64:newcnf=on:nwc=1:tha=off:updr=off_300");
  fallback.push("lrs+1002_2:1_add=large:afp=100000:afq=1.2:amm=off:anc=none:cond=fast:fde=unused:gs=on:gsaa=from_current:gsem=on:ile=on:nm=64:newcnf=on:nwc=1:sas=z3:sd=5:ss=axioms:st=1.2:tha=off:uwa=ground_300");
  fallback.push("lrs+1_32_av=off:bd=off:bs=unit_only:er=known:gsp=on:gs=on:nm=64:newcnf=on:nwc=1.1:sos=on:sp=reverse_arity:urr=ec_only_300");
  fallback.push("ott+1_5:1_afp=4000:afq=1.1:anc=none:bd=off:cond=on:ile=on:nm=64:nwc=1:sas=z3:sac=on:sp=reverse_arity:urr=on:updr=off_300");
  fallback.push("lrs+1011_1_av=off:bd=off:ile=on:irw=on:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1:sp=occurrence_300");
  fallback.push("lrs+11_3:1_av=off:bsr=on:cond=on:fsr=off:ile=on:irw=on:lma=on:nm=64:nwc=1.1:sp=reverse_arity:updr=off_300");
  fallback.push("dis+2_4_afp=10000:afq=1.1:bd=off:bs=on:cond=on:er=filter:ile=on:newcnf=on:nwc=1:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_300");
  fallback.push("ott-1_3:1_av=off:bsr=on:br=off:bce=on:cond=on:fsr=off:fde=unused:irw=on:nm=2:newcnf=on:nwc=2.5:sos=on:sp=occurrence:tha=off:thi=overlap:urr=on:updr=off:uhcvi=on_300");
  fallback.push("lrs+10_3:2_av=off:bd=off:bsr=on:cond=on:fsr=off:gs=on:gsem=off:nm=64:newcnf=on:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:urr=on_300");
  fallback.push("ott+10_2:1_av=off:bd=off:br=off:cond=fast:fsr=off:fde=none:gs=on:gsem=off:irw=on:nm=64:newcnf=on:nwc=1:sos=all:urr=on:updr=off:uhcvi=on_300");
  fallback.push("lrs+4_3_av=off:bd=preordered:fde=none:inw=on:ile=on:nm=64:newcnf=on:nwc=1:tha=off:thf=on:updr=off:uhcvi=on_300");
  fallback.push("dis+1011_8:1_add=off:afp=10000:afq=1.1:anc=none:bce=on:er=filter:gs=on:gsaa=from_current:gsem=off:inw=on:ile=on:lma=on:nm=2:nwc=3:sac=on:urr=on:updr=off_300");
  fallback.push("dis+10_1_afp=10000:afq=1.0:amm=sco:anc=none:bce=on:fde=none:gs=on:gsem=off:inw=on:ile=on:irw=on:lma=on:nm=16:newcnf=on:nwc=1:sas=z3:sos=on:sac=on:sp=occurrence:tha=off:thi=full_300");
  fallback.push("lrs+1004_1_aac=none:add=off:afr=on:afp=10000:afq=1.0:amm=sco:anc=all_dependent:bd=off:cond=fast:fsr=off:gs=on:gsaa=from_current:lcm=reverse:nm=0:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off:thf=on:urr=on:updr=off_300");
  fallback.push("lrs-10_3:2_aac=none:add=off:afr=on:afp=4000:afq=1.4:amm=off:anc=none:bd=off:bsr=on:fsr=off:ile=on:irw=on:lcm=reverse:lma=on:lwlo=on:nm=16:nwc=1:nicw=on:sas=z3:sd=2:ss=axioms:sos=on:sp=occurrence:updr=off_600");
  fallback.push("dis+11_50_aac=none:acc=model:add=large:afr=on:afp=4000:afq=2.0:anc=none:ccuc=first:er=known:fde=unused:gsp=on:gs=on:gsaa=full_model:ile=on:irw=on:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_300");
  fallback.push("lrs+4_8:1_av=off:cond=on:gs=on:gsem=on:irw=on:nm=64:newcnf=on:nwc=1.1:sp=occurrence:tha=off:urr=on:updr=off_300");
  fallback.push("lrs-11_4:1_add=large:afp=1000:afq=1.1:amm=sco:bs=on:cond=on:gs=on:gsem=on:ile=on:nm=2:newcnf=on:nwc=1:sas=z3:sos=on:sp=occurrence:updr=off_300");
  fallback.push("dis+1010_6_av=off:cond=on:er=filter:fsr=off:nm=64:newcnf=on:nwc=1.3:sp=reverse_arity_300");
  fallback.push("lrs+10_128_add=off:afr=on:amm=sco:anc=none:bsr=on:cond=on:ile=on:irw=on:nm=2:nwc=2:nicw=on:sas=z3:updr=off_300");
  fallback.push("ott-1_1_acc=model:add=off:afr=on:afp=4000:afq=1.2:anc=all:bd=preordered:bs=unit_only:bsr=on:ccuc=first:gs=on:gsaa=from_current:ile=on:nm=64:newcnf=on:nwc=1:nicw=on:sac=on:sp=occurrence:tha=off:thi=strong:updr=off_300");
  fallback.push("dis+4_6_av=off:bd=off:bs=on:ile=on:irw=on:lma=on:nm=64:nwc=1_300");
  fallback.push("lrs+10_3:1_afp=1000:afq=1.4:amm=off:anc=none:bsr=on:inw=on:ile=on:lma=on:nm=0:newcnf=on:nwc=1:sas=z3:sac=on:tha=off:urr=on:updr=off_300");
  fallback.push("dis+11_5:1_av=off:br=off:cond=on:fsr=off:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=0:newcnf=on:nwc=1:tha=off:urr=on_300");
  fallback.push("lrs+1011_3:1_add=off:afr=on:afp=4000:afq=2.0:amm=off:anc=none:bce=on:ep=RS:gs=on:ile=on:lma=on:nm=64:newcnf=on:nwc=1.2:sp=occurrence:tha=off_300");
  fallback.push("lrs+11_2:1_add=large:afr=on:afp=1000:afq=1.4:anc=none:cond=fast:fsr=off:fde=unused:gs=on:gsaa=full_model:gsem=on:ile=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.1:tha=off:urr=on:uhcvi=on_300");
  fallback.push("dis+1010_5:1_av=off:cond=on:gsp=on:gs=on:gsem=on:irw=on:lma=on:nm=0:newcnf=on:nwc=1:urr=on:updr=off_300");
  fallback.push("ott+10_2:1_av=off:bce=on:cond=fast:fde=none:irw=on:nm=32:newcnf=on:nwc=1:sos=theory:updr=off_300");
  fallback.push("dis+4_16_acc=model:add=large:afr=on:afp=40000:afq=2.0:amm=off:anc=none:bs=on:ccuc=small_ones:fsr=off:ile=on:nm=4:newcnf=on:nwc=1:nicw=on:sp=reverse_arity_300");
  fallback.push("ott+1011_5:1_add=off:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:bsr=on:inw=on:ile=on:lma=on:nm=2:nwc=1.5:sas=z3:sos=theory:thf=on:updr=off_300");
  fallback.push("lrs+1011_5:4_av=off:bd=off:bs=on:cond=on:er=known:gs=on:gsem=on:inw=on:ile=on:lcm=reverse:nm=6:newcnf=on:nwc=1:sp=occurrence:tha=off:uhcvi=on_300");
  fallback.push("dis+11_5:1_afr=on:afp=40000:afq=2.0:amm=sco:anc=all_dependent:cond=fast:fde=unused:gs=on:gsem=off:ile=on:irw=on:lma=on:nm=2:nwc=1:sos=all:urr=on:uhcvi=on_300");
  fallback.push("dis+1_4_av=off:bd=off:fsr=off:nm=64:newcnf=on:nwc=1:sp=reverse_arity_300");
  fallback.push("dis+1002_2:3_av=off:bs=on:bce=on:cond=fast:ile=on:nm=2:newcnf=on:nwc=1:sp=occurrence:tha=off:thi=strong_300");
  fallback.push("dis+4_4:1_add=off:afp=4000:afq=1.2:amm=sco:anc=none:br=off:cond=fast:ep=RS:fsr=off:inw=on:lma=on:nm=2:newcnf=on:nwc=1:sp=reverse_arity:tha=off:thf=on:urr=on:uhcvi=on_300");
  fallback.push("dis+1010_2:1_add=large:afp=10000:afq=2.0:amm=off:anc=all_dependent:bce=on:cond=fast:ep=R:fsr=off:ile=on:lma=on:nm=64:nwc=1:sac=on:urr=on_300");
  fallback.push("dis+11_4:1_add=large:afr=on:afp=40000:afq=1.1:amm=off:anc=none:br=off:cond=fast:gs=on:gsem=on:ile=on:irw=on:lma=on:nm=2:nwc=1:sas=z3:ss=axioms:st=3.0:sos=all:sp=occurrence:tha=off:urr=on:updr=off:uhcvi=on_300");
  fallback.push("ott+1004_8:1_afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:fde=unused:ile=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sp=reverse_arity:tha=off:updr=off_300");
  fallback.push("ott+11_2_av=off:inw=on:ile=on:irw=on:lcm=reverse:lma=on:nm=6:nwc=1.5:sp=occurrence:updr=off_300");
  fallback.push("lrs+10_3:1_afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:ile=on:irw=on:lma=on:lwlo=on:nm=64:nwc=1:sas=z3:sos=on:sp=reverse_arity_300");
  fallback.push("lrs+11_2:1_afp=1000:afq=1.4:amm=off:anc=none:inw=on:ile=on:irw=on:nm=64:nwc=1:sac=on:tha=off:urr=on_300");
  fallback.push("lrs+10_3:1_add=large:afp=10000:afq=1.1:amm=off:anc=none:cond=on:gs=on:gsem=off:inw=on:ile=on:lma=on:lwlo=on:nm=64:nwc=1:sd=5:ss=axioms:st=1.5:tha=off:urr=on_300");
  fallback.push("lrs+1011_8:1_av=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sp=reverse_arity:tha=off:thi=strong:uwa=ground:urr=on:updr=off_300");
  fallback.push("ott+1011_4_afp=4000:afq=1.1:amm=off:anc=none:bs=unit_only:cond=fast:fsr=off:fde=none:gsp=on:ile=on:irw=on:nm=32:newcnf=on:nwc=1:sas=z3:sp=occurrence:tha=off_300");
  fallback.push("dis+2_3_acc=on:add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:bs=unit_only:br=off:ccuc=first:cond=on:er=filter:ile=on:nm=6:nwc=1:urr=on_300");
  fallback.push("ott+1002_5:1_add=large:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:br=off:cond=on:fsr=off:gs=on:inw=on:irw=on:lma=on:nm=0:newcnf=on:nwc=1:nicw=on:sos=all:tha=off:urr=on_300");
  fallback.push("dis-4_7_acc=on:afp=40000:afq=1.4:anc=all_dependent:bsr=on:br=off:bce=on:ccuc=first:er=filter:fsr=off:fde=unused:gsp=on:ile=on:lcm=reverse:lma=on:nm=4:newcnf=on:nwc=1:nicw=on:sac=on:sp=reverse_arity:tha=off:thi=full:uwa=ground:urr=on:updr=off:uhcvi=on_300");
  fallback.push("lrs+1002_1_av=off:bd=off:fsr=off:fde=none:nm=2:newcnf=on:nwc=1:sp=reverse_arity:uhcvi=on_300");
  fallback.push("dis-2_4_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bce=on:gs=on:inw=on:ile=on:lwlo=on:nm=64:newcnf=on:nwc=1:sas=z3:sos=all:sp=reverse_arity:tha=off:thi=all_300");
  fallback.push("dis+1011_3_aac=none:afp=1000:afq=1.2:anc=all:fde=none:gs=on:gsem=on:inw=on:ile=on:lcm=predicate:lma=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:tha=off:urr=on_900");
  fallback.push("lrs+10_24_av=off:bs=unit_only:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sd=7:ss=axioms:st=1.2:sp=occurrence:tha=off:thf=on:uhcvi=on_600");
  fallback.push("lrs+4_28_afp=10000:afq=1.2:amm=sco:anc=none:bd=off:bce=on:cond=on:fsr=off:ile=on:irw=on:lcm=reverse:nm=16:newcnf=on:nwc=2:sas=z3:sp=occurrence:tha=off:updr=off:uhcvi=on_600");
  fallback.push("lrs+1003_4:1_av=off:bd=preordered:cond=on:fde=unused:gs=on:ile=on:irw=on:nm=64:nwc=1.2:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_900");
  fallback.push("fmb+10_1_av=off:bce=on:fmbes=smt:fmbsr=1.6:fde=none:ile=on:nm=64:updr=off_900");
} // getSmtcomp2018Schedule

// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------

void Schedules::getLtb2017Hh4Schedule(const Property& property, Schedule& sched) {
  sched.push("lrs+10_3_ep=RS:gs=on:gsem=off:nm=1024:nwc=1:stl=300:sd=2:ss=priority:sos=all:av=off_60"); // HH4 1 (4899)
  sched.push("dis+11_4_cond=on:gsp=on:gs=on:nm=0:nwc=1:sd=2:ss=axioms:st=1.5:sos=on:av=off:urr=on:updr=off:uhcvi=on_60"); // HH4 2 (1018)
  sched.push("lrs+11_2:3_br=off:cond=on:fde=none:gs=on:gsem=on:lwlo=on:nm=64:nwc=1:stl=300:sd=1:ss=axioms:st=2.0:sos=all:av=off:sp=occurrence:urr=on:updr=off_60"); // HH4 3 (356)
  sched.push("dis+1002_4_cond=fast:ep=RST:fde=unused:gs=on:gsaa=from_current:gsem=off:nm=0:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:sac=on:add=large:afp=100000:afq=1.0:amm=sco:anc=none:updr=off:uhcvi=on_60"); // HH4 4 (230)
  sched.push("lrs+1011_1_cond=fast:fsr=off:fde=unused:gsp=on:gs=on:gsem=off:gsssp=full:nm=0:nwc=10:stl=300:sd=1:ss=axioms:st=5.0:av=off:sp=occurrence:urr=on_60"); // HH4 5 (179)
  sched.push("ott+2_2:1_bd=off:bsr=unit_only:cond=on:gs=on:nwc=1:sd=3:ss=priority:st=1.5:sos=on:av=off:sp=occurrence:updr=off_60"); // HH4 6 (138)
  sched.push("lrs+11_5:4_bd=off:bsr=unit_only:br=off:fsr=off:fde=none:gsp=on:gs=on:gsem=on:nm=0:nwc=1:stl=300:sd=1:ss=axioms:sos=on:add=off:afp=40000:afq=1.4:amm=sco:urr=on:updr=off:uhcvi=on_60"); // HH4 7 (120)
  sched.push("ott+1011_1_bd=preordered:cond=on:gsp=on:nm=64:nwc=1:sd=3:ss=priority:av=off:sp=reverse_arity:urr=on_60"); // HH4 8 (90)
  sched.push("lrs+11_5_cond=on:ep=RST:fde=none:gsp=on:gs=on:gsem=off:nm=0:nwc=1:stl=300:sd=2:ss=axioms:st=3.0:sos=all:sac=on:add=large:afp=40000:afq=1.4:amm=off:anc=none:urr=ec_only:uhcvi=on_60"); // HH4 10 (70)
  sched.push("lrs+1011_3_bd=off:bsr=on:cond=fast:fde=none:gs=on:gsssp=full:nm=0:nwc=1:stl=300:sd=2:ss=axioms:sos=all:av=off:sp=occurrence_60"); // HH4 11 (58)
  sched.push("lrs-4_5:4_cond=on:gs=on:gsem=on:gsssp=full:nm=64:nwc=1:stl=300:sd=2:ss=axioms:st=2.0:sos=on:sac=on:afp=100000:afq=1.1:amm=sco:anc=none:urr=on_60"); // HH4 12 (44)
  sched.push("dis+1011_3:1_br=off:nm=0:nwc=5:sd=1:ss=axioms:sac=on:afp=40000:afq=1.4:amm=sco:anc=none:urr=on:uhcvi=on_60"); // HH4 13 (38)
  sched.push("lrs+11_3:1_bd=off:bsr=unit_only:fsr=off:gs=on:gsaa=from_current:gsem=off:nm=64:nwc=1:stl=300:sd=2:ss=priority:sac=on:amm=sco:anc=none:sp=reverse_arity:updr=off:uhcvi=on_60"); // HH4 14 (36)
  sched.push("dis+4_3_bd=off:cond=on:fde=unused:gs=on:gsaa=full_model:gsem=off:gsssp=full:nwc=1:sd=3:ss=axioms:st=3.0:sos=on:add=off:afr=on:afp=10000:afq=1.0:amm=off:anc=none:urr=ec_only:updr=off:uhcvi=on_60"); // HH4 15 (32)
  sched.push("dis+1010_5_cond=fast:nm=0:nwc=1:sd=1:ss=axioms:st=1.5:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // HH4 16 (32)
  sched.push("lrs+11_4:1_bd=off:bsr=unit_only:br=off:fsr=off:fde=unused:gsp=on:gs=on:nm=0:nwc=1:stl=300:sd=1:ss=axioms:sos=on:av=off:sp=reverse_arity:urr=on_60"); // HH4 17 (29)
  sched.push("dis+1002_4_cond=on:gs=on:gsem=off:nwc=1:sd=2:ss=axioms:sos=on:av=off:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_60"); // HH4 18 (28)
  sched.push("lrs+11_2:3_cond=on:fde=unused:gs=on:gsaa=full_model:nwc=4:stl=300:sd=2:ss=priority:st=5.0:sac=on:add=off:afr=on:amm=off:anc=none:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // HH4 19 (24)
  sched.push("ott-11_8:1_bsr=unit_only:cond=on:gs=on:gsem=off:gsssp=full:nwc=1.1:sd=2:ss=axioms:sos=on:sac=on:acc=model:add=large:aer=off:afp=40000:afq=2.0:anc=none:sp=reverse_arity:urr=on_60"); // HH4 20 (23)
  sched.push("lrs+1010_2:1_gs=on:lwlo=on:nm=0:nwc=3:stl=300:sd=4:ss=axioms:av=off_60"); // HH4 21 (22)
  sched.push("lrs+1010_4_bsr=unit_only:cond=fast:fsr=off:gs=on:gsaa=from_current:gsem=on:gsssp=full:nm=0:nwc=1:stl=300:sd=1:ss=axioms:st=1.5:sos=on:add=off:aer=off:afr=on:afp=10000:afq=1.0:anc=none:sp=occurrence:urr=on_60"); // HH4 22 (20)
  sched.push("dis+2_1_fsr=off:nwc=1:sd=2:ss=axioms:sos=on:av=off:sp=reverse_arity:updr=off:uhcvi=on_60"); // HH4 23 (17)
  sched.push("ott+2_2:1_cond=fast:fsr=off:fde=unused:gs=on:gsem=off:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // HH4 24 (17)
  sched.push("lrs+1003_8:1_br=off:cond=on:fde=none:gs=on:gsem=off:nm=0:nwc=1:stl=300:sd=1:ss=axioms:sos=on:add=off:afr=on:afp=40000:afq=1.1:amm=off:anc=none:sp=occurrence:urr=on_60"); // HH4 25 (14)
  sched.push("dis+11_2:1_bd=off:cond=fast:fde=unused:gs=on:gsem=on:nwc=1:sd=3:ss=axioms:st=2.0:sos=all:av=off:sp=occurrence_60"); // HH4 26 (14)
  sched.push("lrs+1011_3:1_bd=off:cond=fast:fsr=off:fde=unused:gs=on:nm=0:nwc=5:stl=300:sd=2:ss=axioms:afp=100000:afq=1.4:amm=off:anc=none:sp=occurrence:urr=on_60"); // HH4 27 (14)
  sched.push("dis+1011_3_cond=on:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:sac=on:afr=on:afp=1000:afq=1.4:anc=none:sp=occurrence:updr=off:uhcvi=on_60"); // HH4 28 (13)
  sched.push("dis+11_2:1_fde=none:gsp=on:nwc=1:sd=2:ss=axioms:sos=all:av=off:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // HH4 29 (13)
  sched.push("lrs+11_3_bsr=unit_only:cond=fast:fsr=off:fde=none:gsp=on:nwc=5:stl=300:sd=3:ss=priority:st=2.0:av=off:updr=off:uhcvi=on_60"); // HH4 30 (12)
  sched.push("lrs+11_5:1_cond=on:gs=on:gsssp=full:lwlo=on:nwc=1:stl=300:sd=1:ss=axioms:st=3.0:av=off:urr=on_60"); // HH4 31 (11)
  sched.push("dis+1_5_bd=preordered:bs=unit_only:ccuc=small_ones:cond=on:fsr=off:gs=on:gsem=on:nm=0:nwc=1:sd=1:ss=axioms:st=1.5:sos=all:aac=none:acc=model:add=off:aer=off:afr=on:afp=100000:afq=1.2:anc=all_dependent:urr=ec_only:updr=off:uhcvi=on_60"); // HH4 32 (10)
  sched.push("lrs+11_4_bd=off:cond=fast:fde=unused:gs=on:nwc=1:stl=300:sd=3:ss=axioms:st=5.0:sos=all:afr=on:afp=100000:afq=1.2:amm=sco:anc=none:updr=off:uhcvi=on_60"); // HH4 33 (10)
  sched.push("lrs+11_8:1_br=off:cond=fast:fde=none:gs=on:gsaa=from_current:gsem=on:nm=0:nwc=2:stl=300:sd=2:ss=axioms:st=1.5:sac=on:add=off:afp=40000:afq=1.4:anc=none:sp=reverse_arity:urr=on_60"); // HH4 34 (9)
  sched.push("dis+1003_1_ccuc=first:fsr=off:fde=unused:gsp=on:gs=on:gsem=on:nm=64:nwc=1:sd=2:ss=axioms:st=3.0:sos=on:acc=model:add=large:sp=reverse_arity:uhcvi=on_60"); // HH4 35 (9)
  sched.push("dis+11_3_br=off:cond=on:ep=RST:fsr=off:fde=none:gsp=on:gs=on:nwc=1:sd=2:ss=axioms:sos=all:sac=on:add=off:afp=40000:afq=1.0:amm=sco:anc=none:sp=reverse_arity:urr=on:updr=off_60"); // HH4 36 (8)
  sched.push("dis+10_5:4_ep=R:gs=on:gsaa=from_current:nm=64:nwc=1:sd=1:ss=axioms:sos=on:add=large:aer=off:afp=4000:afq=1.1:anc=none:updr=off:uhcvi=on_60"); // HH4 37 (8)
  sched.push("dis+11_3:1_br=off:cond=fast:fde=unused:gs=on:gsem=off:nm=0:nwc=1.7:sd=1:ss=axioms:st=1.5:sac=on:add=off:aer=off:afr=on:afp=10000:afq=1.4:anc=none:urr=on:uhcvi=on_60"); // HH4 38 (8)
  sched.push("dis+10_5_bd=off:cond=fast:fde=unused:gsp=on:gs=on:gsem=off:gsssp=full:nwc=1:sd=3:ss=axioms:st=2.0:sos=on:sac=on:add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:sp=occurrence:urr=on:uhcvi=on_60"); // HH4 39 (8)
  sched.push("ott+11_4_cond=fast:fsr=off:fde=none:gsp=on:gs=on:gsssp=full:lcm=predicate:nm=64:nwc=1.7:sd=2:ss=priority:st=1.2:av=off:sp=occurrence:urr=on:uhcvi=on_60"); // HH4 40 (8)
  sched.push("ott+11_2:1_bd=preordered:ccuc=small_ones:cond=fast:fde=unused:gs=on:gsem=on:nm=1024:nwc=3:sd=3:ss=priority:st=1.2:acc=model:add=large:afr=on:afp=100000:afq=1.4:amm=off:anc=none:sp=occurrence:uhcvi=on_60"); // HH4 41 (8)
  sched.push("ott+1011_5:4_fde=unused:gs=on:gsem=off:nwc=1.3:sd=4:ss=priority:st=5.0:add=off:afp=1000:afq=1.2:amm=sco:sp=reverse_arity:urr=on_60"); // HH4 42 (7)
  sched.push("lrs+11_5:4_cond=on:fde=none:gs=on:gsem=off:gsssp=full:nwc=1:stl=300:sd=2:ss=axioms:st=2.0:sos=on:av=off:sp=occurrence:uhcvi=on_60"); // HH4 43 (7)
  sched.push("lrs+11_2_bd=off:cond=fast:fde=unused:gsp=on:nwc=1:nicw=on:stl=300:sd=2:ss=priority:st=1.2:sos=all:sac=on:aac=none:aer=off:afr=on:afp=10000:afq=2.0:anc=all:sp=reverse_arity_60"); // HH4 44 (7)
  sched.push("dis+1003_5:4_fde=none:gs=on:gsem=on:gsssp=full:nm=64:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:av=off:sp=occurrence:urr=ec_only_60"); // HH4 45 (7)
  sched.push("dis+11_1_br=off:cond=fast:ep=RST:fsr=off:fde=unused:gsp=on:gs=on:gsem=off:nm=0:nwc=1.1:sd=1:ss=axioms:add=large:aer=off:afr=on:anc=none:urr=on:updr=off_60"); // HH4 46 (6)
  sched.push("dis-2_5_bd=off:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:nm=1024:nwc=1:sd=5:ss=axioms:sos=on:sac=on:add=off:aer=off:afr=on:afp=1000:afq=1.2:anc=none:urr=ec_only:updr=off_60"); // HH4 47 (6)
  sched.push("lrs-1_5_cond=fast:fde=none:gs=on:nm=0:nwc=1.1:stl=300:sd=1:ss=axioms:st=3.0:sos=on:av=off:sp=occurrence:uhcvi=on_60"); // HH4 48 (6)
  sched.push("dis+1010_4_cond=on:fde=unused:gs=on:gsem=on:nm=0:nwc=1:sd=2:ss=axioms:st=3.0:sos=on:av=off:updr=off_60"); // HH4 49 (6)
  sched.push("lrs+10_5:4_fde=unused:gs=on:gsem=on:gsssp=full:nm=0:nwc=5:stl=300:sd=1:ss=axioms:av=off:updr=off:uhcvi=on_60"); // HH4 50 (6)
  sched.push("dis+11_4:1_bsr=unit_only:ccuc=small_ones:fsr=off:nm=64:nwc=3:sd=1:ss=axioms:st=1.2:sos=on:acc=on:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:sp=occurrence:updr=off_60"); // HH4 51 (6)
  sched.push("ott+1011_1_cond=on:fsr=off:fde=none:gs=on:gsem=off:nm=0:nwc=10:sd=1:ss=axioms:st=2.0:av=off:sp=occurrence:urr=on:updr=off_60"); // HH4 52 (6)
  sched.push("dis+1002_1_cond=on:ep=RSTC:fsr=off:gs=on:nwc=1:sd=1:ss=axioms:sos=on:av=off:sp=reverse_arity_60"); // HH4 53 (5)
  sched.push("lrs+1003_6_cond=on:gs=on:gsem=off:gsssp=full:nm=0:nwc=2.5:stl=300:sd=3:ss=priority:av=off:sp=reverse_arity:updr=off_60"); // HH4 54 (5)
  sched.push("dis-2_3_bd=off:cond=fast:fsr=off:gs=on:gsem=off:nwc=1:sd=2:ss=axioms:st=5.0:sos=on:av=off:sp=occurrence:urr=ec_only:uhcvi=on_60"); // HH4 55 (5)
  sched.push("dis+1011_4_br=off:cond=on:fde=none:gs=on:gsem=on:gsssp=full:nm=1024:nwc=1:sd=3:ss=axioms:sos=on:sac=on:add=large:afp=100000:afq=1.2:amm=sco:anc=all_dependent:urr=on:uhcvi=on_60"); // HH4 56 (5)
  sched.push("lrs+10_4_bsr=unit_only:cond=fast:ep=RST:gs=on:gsem=on:gsssp=full:nm=0:nwc=1:stl=300:sd=2:ss=priority:st=1.5:sos=all:av=off:sp=reverse_arity_60"); // HH4 57 (5)
  sched.push("lrs+4_5:4_bd=off:cond=on:fsr=off:fde=none:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:stl=300:sd=2:ss=axioms:st=1.2:sos=on:av=off:sp=reverse_arity_60"); // HH4 58 (5)
  sched.push("ott+11_3:1_bs=unit_only:bsr=unit_only:cond=fast:fsr=off:fde=none:gsp=on:nm=64:nwc=1.2:sd=5:ss=priority:st=1.2:av=off:sp=reverse_arity:updr=off_60"); // HH4 59 (5)
  sched.push("dis+10_3:1_cond=on:fsr=off:fde=unused:nwc=1:sd=1:ss=priority:st=5.0:sos=all:add=large:aer=off:afr=on:afp=40000:afq=1.4_60"); // HH4 60 (4)
  sched.push("lrs+11_4:1_cond=fast:fde=none:nm=0:nwc=1:stl=300:sd=3:ss=priority:st=2.0:av=off:sp=occurrence:urr=ec_only_60"); // HH4 61 (4)
  sched.push("lrs-3_4_bd=off:bsr=unit_only:fde=unused:gs=on:gsaa=full_model:nwc=1:stl=300:sd=3:ss=axioms:sos=on:sac=on:aer=off:afr=on:afp=40000:afq=1.4:anc=none:updr=off:uhcvi=on_60"); // HH4 62 (4)
  sched.push("lrs+1011_2:3_bsr=unit_only:fsr=off:fde=none:gs=on:gsem=on:nm=64:nwc=2.5:stl=300:sd=3:ss=priority:st=3.0:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // HH4 63 (4)
  sched.push("ott+1010_3:1_cond=fast:fde=unused:nm=64:nwc=1.7:sd=3:ss=priority:av=off:sp=occurrence:updr=off_60"); // HH4 64 (4)
  sched.push("dis+2_4:1_bsr=unit_only:br=off:cond=fast:fde=none:lcm=reverse:lwlo=on:nm=0:nwc=1:sd=1:ss=axioms:sos=on:av=off:sp=occurrence:urr=on_60"); // HH4 65 (3)
  sched.push("dis+11_1_cond=fast:ep=RST:fde=none:nm=1024:nwc=2:sd=2:ss=priority:st=1.5:add=off:afp=100000:afq=1.1:amm=off:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // HH4 66 (3)
  sched.push("lrs+4_5:4_bd=off:bsr=unit_only:fsr=off:gs=on:nm=0:nwc=1:stl=300:sd=2:ss=axioms:st=1.5:sos=on:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // HH4 67 (3)
  sched.push("dis+1010_3_bsr=unit_only:gs=on:gsaa=from_current:gsem=off:gsssp=full:nm=64:nwc=1:sd=1:ss=axioms:sos=on:afp=10000:afq=1.2:amm=sco:anc=none:sp=reverse_arity_60"); // HH4 68 (3)
  sched.push("lrs+11_3_cond=fast:gs=on:nm=0:nwc=1.3:stl=300:sd=2:ss=priority:av=off:sp=reverse_arity:updr=off_60"); // HH4 69 (3)
  sched.push("dis+11_3_cond=fast:gsp=on:gs=on:gsaa=from_current:gsem=on:nm=64:nwc=1:sd=3:ss=priority:sos=on:add=off:afp=10000:afq=1.2:amm=sco:anc=none:sp=reverse_arity:urr=on:updr=off:uhcvi=on_60"); // HH4 70 (3)
  sched.push("lrs+11_3_bd=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:nwc=1:stl=300:sd=4:ss=axioms:st=1.5:sos=all:av=off:sp=reverse_arity:uhcvi=on_60"); // HH4 71 (3)
  sched.push("dis+10_3:1_bsr=unit_only:cond=fast:fde=none:nm=64:nwc=1:sd=2:ss=axioms:sos=all:av=off:sp=reverse_arity:updr=off_60"); // HH4 72 (3)
  sched.push("lrs+11_4_ep=RST:fde=unused:gs=on:gsaa=from_current:gsssp=full:nwc=1:stl=300:sd=1:ss=axioms:st=5.0:sos=all:sac=on:aer=off:afr=on:afp=40000:afq=2.0:anc=none:sp=reverse_arity:urr=on:updr=off:uhcvi=on_60"); // HH4 73 (3)
  sched.push("dis+11_2_bd=preordered:bs=unit_only:fsr=off:fde=none:gs=on:gsem=on:nm=0:nwc=3:sd=3:ss=axioms:st=1.5:sac=on:acc=on:add=off:afr=on:afp=100000:afq=1.2:amm=sco:anc=all:sp=occurrence:uhcvi=on_60"); // HH4 74 (3)
  sched.push("lrs+11_4_fde=unused:gsp=on:lcm=predicate:nm=0:nwc=1.3:stl=300:sd=1:ss=axioms:st=2.0:av=off:sp=occurrence:urr=on:uhcvi=on_60"); // HH4 75 (3)
  sched.push("lrs+11_3:1_bd=off:bsr=unit_only:fsr=off:fde=unused:gs=on:gsem=on:nm=0:nwc=1:stl=300:sd=2:ss=axioms:add=large:afp=40000:afq=1.1:sp=reverse_arity_60"); // HH4 76 (3)
  sched.push("lrs+11_3:1_bd=off:bsr=unit_only:cond=on:fsr=off:gs=on:gsem=on:nm=64:nwc=1:stl=300:sd=1:ss=axioms:st=1.5:av=off:sp=reverse_arity:updr=off_60"); // HH4 77 (2)
  sched.push("dis+11_3_ep=RST:fde=unused:gs=on:gsaa=from_current:gsem=off:gsssp=full:nm=0:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sac=on:amm=sco:anc=none:urr=ec_only:updr=off_60"); // HH4 78 (2)
  sched.push("ott+11_5:1_br=off:cond=on:ep=RST:fsr=off:gs=on:gsem=on:gsssp=full:nwc=1:sd=3:ss=priority:sos=all:av=off:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // HH4 79 (2)
  sched.push("lrs+11_5_bd=off:bsr=unit_only:gs=on:gsaa=from_current:gsem=off:nwc=1:stl=300:sd=2:ss=axioms:st=3.0:sos=all:sac=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:sp=occurrence:updr=off_60"); // HH4 80 (2)
  sched.push("dis+11_5_cond=on:ep=RST:gs=on:lwlo=on:nm=64:nwc=2:sd=1:ss=axioms:st=2.0:sac=on:afp=10000:afq=1.2:anc=none:updr=off_60"); // HH4 81 (2)
  sched.push("ott+1010_3_cond=on:fsr=off:fde=unused:nm=0:nwc=1.2:sd=2:ss=priority:st=1.2:av=off:sp=reverse_arity:urr=on:updr=off:uhcvi=on_60"); // HH4 82 (2)
  sched.push("lrs+1010_2_bs=unit_only:bsr=unit_only:ccuc=first:cond=on:fsr=off:fde=unused:gs=on:gsssp=full:nm=0:nwc=1.5:nicw=on:stl=300:sd=2:ss=axioms:st=5.0:sos=on:sac=on:acc=on:add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:sp=reverse_arity:uhcvi=on_60"); // HH4 83 (2)
  sched.push("lrs+11_5_bd=off:cond=fast:gs=on:gsssp=full:nwc=1.1:stl=300:sd=2:ss=axioms:st=1.2:sos=all:av=off:uhcvi=on_60"); // HH4 84 (2)
  sched.push("lrs+11_5_fde=unused:gs=on:gsem=off:nwc=1:stl=300:sd=1:ss=priority:st=1.2:sos=all:sac=on:aer=off:afp=40000:afq=1.2:anc=all:sp=occurrence_60"); // HH4 85 (2)
  sched.push("lrs+11_3_fsr=off:fde=unused:gs=on:nm=64:nwc=1.7:stl=300:sd=3:ss=axioms:st=2.0:av=off_60"); // HH4 87 (2)
  sched.push("lrs+11_3_bd=off:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsem=on:gsssp=full:nm=0:nwc=1:stl=300:sd=3:ss=priority:st=1.5:av=off:sp=reverse_arity_60"); // HH4 88 (2)
  sched.push("ott+1004_4:1_bs=on:cond=on:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=off:nm=0:nwc=1.5:sd=2:ss=axioms:st=5.0:sac=on:add=large:afr=on:afp=1000:afq=1.1:anc=none:urr=on:updr=off_60"); // HH4 89 (2)
  sched.push("lrs+10_8:1_bd=off:fsr=off:fde=none:gs=on:gsem=on:lwlo=on:nwc=1:stl=300:sd=10:ss=priority:add=off:aer=off:afp=100000:afq=1.4:sp=reverse_arity:urr=on:uhcvi=on_60"); // HH4 90 (2)
  sched.push("dis+10_24_cond=fast:ep=RST:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:gsssp=full:nm=0:nwc=1:sd=3:ss=axioms:st=5.0:sos=on:sac=on:add=off:afp=1000:afq=1.4:amm=sco:anc=none:sp=occurrence_60"); // HH4 91 (1)
  sched.push("lrs+11_4:1_cond=on:ep=RS:fsr=off:lwlo=on:nm=0:nwc=1:stl=300:sos=all:av=off:sp=reverse_arity:uhcvi=on_60"); // HH4 92 (1)
  sched.push("dis+2_5_bsr=unit_only:cond=on:fsr=off:nwc=1:sd=10:ss=priority:st=2.0:sos=on:av=off:sp=occurrence:urr=ec_only_60"); // HH4 93 (1)
  sched.push("lrs-3_8:1_bsr=unit_only:cond=fast:fsr=off:fde=none:gs=on:gsem=off:nm=0:nwc=1:stl=300:sd=4:ss=priority:st=3.0:av=off:sp=occurrence_60"); // HH4 94 (1)
  sched.push("lrs+10_2:3_fsr=off:fde=unused:gs=on:gsem=on:nm=64:nwc=1:stl=300:sd=5:ss=priority:st=1.2:sos=on:av=off:sp=reverse_arity:updr=off_60"); // HH4 95 (1)
  sched.push("lrs+1010_8:1_bsr=on:fsr=off:fde=unused:nm=0:nwc=1:stl=300:sd=2:ss=axioms:av=off:sp=reverse_arity:uhcvi=on_60"); // HH4 96 (1)
  sched.push("lrs+1003_4:1_bd=off:bs=unit_only:bsr=unit_only:fde=none:gsp=on:nm=0:nwc=1:stl=300:sd=3:ss=axioms:sos=all:sac=on:aac=none:add=large:afr=on:afp=4000:afq=1.1:amm=sco:anc=none:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // HH4 97 (1)
  sched.push("lrs+1003_10_bsr=unit_only:br=off:fsr=off:fde=none:nm=64:nwc=2:stl=300:sd=4:ss=axioms:st=1.2:sos=all:sac=on:add=large:afr=on:afp=40000:afq=1.1:amm=off:anc=all:urr=on_60"); // HH4 98 (1)
  sched.push("dis+1004_5_cond=fast:fde=unused:gs=on:lwlo=on:nwc=1:sd=2:ss=axioms:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // HH4 99 (1)
  sched.push("dis+11_4_bd=off:cond=on:fde=unused:gsp=on:gs=on:gsem=off:nm=0:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:afr=on:afp=1000:afq=1.0:amm=sco:anc=none:sp=reverse_arity:urr=on:updr=off:uhcvi=on_60"); // HH4 100 (1)
  sched.push("lrs+11_2:3_bd=off:bs=unit_only:bsr=unit_only:cond=fast:fsr=off:gsp=on:lcm=reverse:nm=0:nwc=1.1:stl=300:sd=1:ss=axioms:st=1.5:sos=all:av=off_60"); // HH4 101 (1)
  sched.push("lrs+11_5:4_bd=off:bsr=unit_only:cond=fast:fsr=off:fde=none:gsp=on:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1:stl=300:sd=2:ss=axioms:av=off:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // HH4 102 (1)
  sched.push("dis+4_4_br=off:cond=fast:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=off:nm=0:nwc=1:sd=1:ss=axioms:st=1.2:add=off:afp=1000:afq=2.0:anc=none:urr=on:updr=off_60"); // HH4 105 (1)
  sched.push("lrs+1004_8_bd=off:bsr=unit_only:br=off:cond=fast:fde=unused:nm=64:nwc=1.5:stl=300:sd=3:ss=priority:st=3.0:av=off:sp=reverse_arity:urr=on_60"); // HH4 106 (1)
  sched.push("lrs+11_2_bsr=unit_only:fsr=off:fde=none:gsp=on:gs=on:nwc=1:stl=300:sd=1:ss=axioms:st=3.0:sos=on:add=off:afp=10000:afq=2.0:amm=off:anc=none:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // HH4 107 (1)
  sched.push("dis+10_4_bd=off:fsr=off:fde=none:gsp=on:gs=on:gsaa=from_current:gsem=on:gsssp=full:nm=64:nwc=1:sd=2:ss=axioms:st=3.0:sos=on:add=large:aer=off:afp=4000:afq=1.1:anc=none:sp=occurrence:urr=ec_only:updr=off_60"); // HH4 108 (1)
  sched.push("dis+10_4_cond=fast:ep=RST:fsr=off:nwc=1:sd=3:ss=axioms:sos=all:av=off_60"); // HH4 109 (1)
  sched.push("dis+1_5_cond=on:ep=RST:fsr=off:fde=none:gsp=on:gs=on:gsem=off:nm=0:nwc=1:sd=2:ss=priority:st=3.0:sos=all:av=off:urr=on_60"); // HH4 110 (1)
  sched.push("dis+2_7_bd=off:cond=fast:fsr=off:gs=on:gsem=off:nm=64:nwc=1.1:sd=3:ss=axioms:st=3.0:sos=on:av=off:sp=occurrence:uhcvi=on_60"); // HH4 111 (1)
  sched.push("lrs-3_4_bsr=unit_only:gs=on:nwc=1:stl=300:sd=2:ss=axioms:st=3.0:sos=on:sac=on:add=off:afr=on:afp=1000:afq=1.4:amm=sco:anc=none:sp=reverse_arity:uhcvi=on_60"); // HH4 112 (1)
  sched.push("dis+1004_3:1_fsr=off:gs=on:gsem=off:gsssp=full:nm=0:nwc=1:sd=2:ss=axioms:sos=on:sac=on:add=large:afp=40000:afq=1.2:urr=ec_only:uhcvi=on_60"); // HH4 113 (1)
  sched.push("lrs+1003_4_bd=off:bsr=unit_only:cond=on:gs=on:gsem=off:nm=0:nwc=1:stl=300:sd=2:ss=axioms:sos=on:av=off:sp=occurrence:urr=on:updr=off_60"); // HH4 114 (1)
  sched.push("lrs+11_5_bd=off:cond=fast:fsr=off:fde=none:nm=0:nwc=1:stl=300:sd=2:ss=axioms:st=3.0:sos=all:av=off:updr=off:uhcvi=on_60"); // HH4 115 (1)
  sched.push("dis+4_5_bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsaa=full_model:gsem=off:gsssp=full:nwc=1:sd=3:ss=axioms:st=2.0:sos=on:afr=on:afp=10000:afq=1.2:anc=none:urr=on_60"); // HH4 116 (1)
  sched.push("lrs+11_5_fsr=off:fde=unused:gs=on:gsaa=from_current:gsssp=full:nwc=1:stl=300:sd=4:ss=axioms:sos=on:add=off:afp=10000:afq=1.1:amm=sco:anc=none:sp=reverse_arity:urr=on:uhcvi=on_60"); // HH4 117 (1)
  sched.push("dis+11_3:1_fsr=off:fde=none:nwc=1:sd=1:ss=priority:st=5.0:add=off:aer=off:afr=on:afp=100000:afq=1.1:sp=reverse_arity:urr=on:updr=off_60"); // HH4 118 (1)
  sched.push("dis+11_4:1_cond=fast:gs=on:gsem=on:nm=64:nwc=1.1:sd=1:ss=axioms:st=2.0:av=off:sp=occurrence:urr=on_60"); // HH4 119 (1)
  sched.push("lrs+1010_5:1_cond=fast:fde=none:gs=on:gsaa=from_current:gsem=on:lwlo=on:nwc=1.2:stl=300:sd=2:ss=priority:st=3.0:sac=on:add=large:aer=off:afr=on:afp=40000:afq=1.0:anc=all:uhcvi=on_60"); // HH4 120 (1)
  sched.push("lrs+1002_3:1_bd=preordered:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=off:nm=0:nwc=3:stl=300:sd=4:ss=priority:sac=on:add=large:afp=10000:afq=1.0:amm=off:anc=none:uhcvi=on_60"); // HH4 122 (1)
  sched.push("dis+4_5:4_cond=on:fsr=off:fde=none:lwlo=on:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:av=off:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_60"); // HH4 123 (1)
  sched.push("ott+11_2:1_gs=on:gsem=on:gsssp=full:nm=0:nwc=1:sd=2:ss=axioms:st=1.5:sac=on:add=large:afp=100000:afq=1.2:amm=sco:anc=all:sp=occurrence:updr=off:uhcvi=on_60"); // HH4 125 (1)
  sched.push("dis+1002_8_bd=off:fsr=off:fde=unused:gs=on:gsem=on:nwc=1:sd=4:ss=priority:sos=on:av=off:sp=occurrence_60"); // HH4 126 (1)
  sched.push("lrs+11_3_cond=fast:ep=RST:fde=unused:gs=on:gsem=on:nwc=1:stl=300:sd=3:ss=axioms:st=5.0:sos=all:av=off:updr=off:uhcvi=on_60"); // HH4 127 (1)
  sched.push("lrs+4_3:1_cond=fast:fsr=off:fde=unused:gs=on:gsem=off:lwlo=on:nm=0:nwc=1.7:stl=300:av=off:sp=reverse_arity:updr=off_60"); // HH4 128 (1)
  sched.push("lrs-3_1_bd=off:cond=on:fde=none:gs=on:lcm=reverse:nm=0:nwc=1.1:stl=300:sd=2:ss=axioms:st=1.5:av=off:updr=off:uhcvi=on_60"); // HH4 130 (1)
  sched.push("lrs+11_5_bd=off:ccuc=first:fde=none:gs=on:lcm=reverse:nm=0:nwc=1:stl=300:sd=2:ss=priority:st=1.2:sos=all:aac=none:acc=model:afr=on:afp=1000:afq=1.1:anc=none:updr=off:uhcvi=on_60"); // HH4 131 (1)
  sched.push("lrs+11_5:4_cond=fast:fde=none:gs=on:gsaa=from_current:gsem=on:nwc=1:stl=300:sd=7:ss=axioms:st=3.0:sos=all:afp=10000:afq=1.1:amm=sco:anc=none:sp=reverse_arity:updr=off:uhcvi=on_60"); // HH4 132 (1)
  sched.push("dis+11_6_fsr=off:fde=none:gs=on:gsem=on:gsssp=full:lwlo=on:nm=0:nwc=1:sd=3:ss=axioms:sos=all:add=off:afr=on:afp=4000:afq=1.0:amm=sco:anc=all:sp=occurrence:urr=ec_only:uhcvi=on_60"); // HH4 133 (1)
  sched.push("lrs+1010_3:2_bd=off:bsr=unit_only:cond=fast:nwc=4:stl=300:sd=1:ss=axioms:st=3.0:sac=on:add=large:afp=10000:afq=1.2:amm=sco:sp=reverse_arity:updr=off:uhcvi=on_60"); // HH4 134 (1)
  sched.push("dis+1004_3:1_cond=fast:fde=unused:nm=0:nwc=1:sd=1:ss=axioms:st=1.2:sos=on:av=off:sp=reverse_arity:updr=off:uhcvi=on_60"); // HH4 135 (1)
  sched.push("dis+4_3_bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsssp=full:lwlo=on:nm=64:nwc=1:ss=axioms:st=2.0:sos=on:av=off:sp=occurrence:updr=off_60"); // HH4 136 (1)
  sched.push("lrs-10_24_bd=off:fsr=off:lcm=reverse:nm=0:nwc=1:stl=300:sd=1:ss=axioms:sos=on:av=off:sp=occurrence_60"); // HH4 137 (1)
  sched.push("ott+11_2:1_cond=fast:nm=0:nwc=2.5:sd=2:ss=priority:st=1.2:av=off:sp=occurrence:urr=on:updr=off_60"); // HH4 139 (1)
}

// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------

void Schedules::getLtb2017IsaSchedule(const Property& property, Schedule& sched) {
  sched.push("dis+1002_3_gs=on:gsem=off:nwc=1.2:sd=2:ss=axioms:st=3.0:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // ISA 1 (1149)
  sched.push("dis+1011_3:2_bsr=unit_only:cond=fast:nwc=3:nicw=on:sd=3:ss=priority:add=off:afr=on:afp=10000:afq=1.2:uhcvi=on_60"); // ISA 2 (347)
  sched.push("lrs+1010_1_cond=on:fde=none:gs=on:gsem=off:nwc=1:stl=300:sd=1:ss=axioms:st=3.0:sos=on:sac=on:afp=10000:afq=1.1:amm=sco:anc=none:urr=on:updr=off_60"); // ISA 3 (174)
  sched.push("lrs-2_3_ep=RS:gs=on:gsaa=from_current:nwc=1:stl=300:sd=2:ss=axioms:sos=on:sac=on:afr=on:afp=40000:afq=1.0:amm=off:anc=none:sp=reverse_arity:uhcvi=on_60"); // ISA 4 (93)
  sched.push("dis+1011_5_fsr=off:fde=unused:nm=64:nwc=3:sd=2:ss=priority:av=off:sp=occurrence:uhcvi=on_60"); // ISA 5 (58)
  sched.push("dis+1002_4_cond=on:gs=on:gsem=off:nwc=1:sd=1:ss=axioms:sos=on:sac=on:afr=on:afp=1000:afq=1.2:amm=sco:anc=none:sp=occurrence:uhcvi=on_60"); // ISA 6 (52)
  sched.push("dis+1002_4_ep=RST:fsr=off:gs=on:gsem=off:lwlo=on:nwc=1:sd=4:ss=axioms:st=1.5:sos=on:aer=off:afr=on:afp=40000:afq=1.2:anc=none_60"); // ISA 7 (39)
  sched.push("lrs+1011_3:2_bd=off:cond=on:gsp=on:gs=on:gsem=on:nm=0:nwc=4:stl=300:sd=1:ss=axioms:aer=off:afr=on:afp=40000:afq=1.1:anc=all_dependent:sp=reverse_arity:updr=off_60"); // ISA 8 (34)
  sched.push("dis+1011_1_bsr=on:ccuc=first:nm=0:nwc=4:sd=2:ss=priority:acc=model:add=large:afr=on:amm=off:anc=none:updr=off:uhcvi=on_60"); // ISA 9 (32)
  sched.push("lrs+1002_4_bd=off:fde=none:gs=on:gsaa=from_current:gsem=off:gsssp=full:nwc=1:stl=300:sd=3:ss=axioms:st=5.0:sos=on:aer=off:afp=100000:afq=1.1:anc=none:sp=reverse_arity_60"); // ISA 10 (29)
  sched.push("dis+1002_5_cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=off:gsssp=full:nwc=1:sd=1:ss=axioms:st=5.0:sos=on:sac=on:add=large:afp=40000:afq=1.1:amm=off:anc=none:sp=reverse_arity:updr=off_60"); // ISA 11 (25)
  sched.push("dis+1011_3_fde=unused:nm=64:nwc=1:sd=2:ss=axioms:st=5.0:add=off:aer=off:afp=10000:afq=1.0:sp=occurrence_60"); // ISA 12 (20)
  sched.push("dis+1011_3:1_cond=fast:ep=RS:nm=0:nwc=1.7:sd=2:ss=priority:st=1.2:add=off:afp=10000:afq=1.2:amm=sco:anc=all:sp=occurrence:updr=off:uhcvi=on_60"); // ISA 13 (16)
  sched.push("dis+1002_5_cond=on:ep=RST:fsr=off:fde=unused:gs=on:gsem=on:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:sac=on:add=off:afr=on:amm=sco:anc=none:updr=off:uhcvi=on_60"); // ISA 14 (16)
  sched.push("dis+1011_5_cond=on:er=filter:fde=none:nm=64:nwc=3:sd=2:ss=priority:st=2.0:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // ISA 15 (12)
  sched.push("lrs+10_3:1_cond=on:fde=none:gs=on:gsem=off:gsssp=full:nwc=1.2:stl=300:sd=1:ss=priority:sos=on:sac=on:add=off:afp=1000:afq=1.4:amm=sco:anc=all:sp=reverse_arity:urr=on:updr=off:uhcvi=on_60"); // ISA 16 (12)
  sched.push("lrs+11_5_br=off:cond=on:fde=none:gs=on:nwc=1:stl=300:sd=2:ss=axioms:st=3.0:sos=all:add=off:afr=on:afp=40000:afq=1.4:anc=none:sp=reverse_arity:urr=on_60"); // ISA 17 (10)
  sched.push("dis+1002_3_bd=off:fde=unused:gs=on:gsaa=from_current:gsem=off:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:afr=on:amm=sco:anc=none:sp=occurrence_60"); // ISA 18 (10)
  sched.push("lrs+1011_4:1_fsr=off:fde=unused:gs=on:gsem=on:gsssp=full:nm=64:nwc=4:stl=300:sd=1:ss=priority:st=3.0:aac=none:acc=on:afr=on:afp=40000:afq=1.2:amm=sco:anc=all:sp=reverse_arity:updr=off:uhcvi=on_60"); // ISA 20 (9)
  sched.push("dis+1002_50_fde=unused:nwc=1:sd=2:ss=axioms:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // ISA 21 (8)
  sched.push("ott+11_4_cond=fast:fde=none:gs=on:gsem=on:gsssp=full:nwc=1:sd=2:ss=axioms:sos=on:av=off:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // ISA 22 (8)
  sched.push("dis-3_3_ep=RST:fde=none:nm=64:nwc=1:sd=4:ss=axioms:sos=on:av=off:sp=occurrence:uhcvi=on_60"); // ISA 23 (7)
  sched.push("dis+1010_7_fsr=off:fde=unused:nm=0:nwc=1.3:nicw=on:sd=3:ss=priority:afr=on:afp=100000:afq=1.0:amm=sco:anc=none:updr=off:uhcvi=on_60"); // ISA 24 (7)
  sched.push("dis+1002_4_cond=fast:ep=RST:fsr=off:nwc=1:sd=3:ss=axioms:st=2.0:sos=on:afp=10000:afq=1.1:amm=sco:sp=occurrence:uhcvi=on_60"); // ISA 25 (6)
  sched.push("ott+1011_2_bd=off:ccuc=first:cond=on:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=on:nm=64:nwc=1.3:sd=3:ss=priority:st=1.2:sac=on:acc=on:add=off:afp=4000:afq=1.4:amm=sco:anc=none:urr=ec_only:updr=off:uhcvi=on_60"); // ISA 26 (6)
  sched.push("dis+1002_3_bd=off:gs=on:gsem=on:nwc=1.1:sd=7:ss=axioms:st=1.2:sos=on:av=off:sp=reverse_arity:updr=off_60"); // ISA 27 (5)
  sched.push("dis+11_2:3_cond=on:gs=on:gsem=off:gsssp=full:lcm=reverse:nwc=1:sd=1:ss=axioms:st=1.5:add=off:aer=off:afr=on:afp=1000:afq=2.0:anc=all_dependent:sp=reverse_arity:updr=off:uhcvi=on_60"); // ISA 28 (5)
  sched.push("dis+1002_3_cond=fast:ep=RSTC:fsr=off:gs=on:gsem=off:lwlo=on:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:av=off:sp=occurrence:uhcvi=on_60"); // ISA 30 (4)
  sched.push("lrs+11_4_ccuc=small_ones:fde=none:gs=on:gsaa=from_current:gsem=off:gsssp=full:nm=0:nwc=1.2:stl=300:sd=1:ss=axioms:st=3.0:sac=on:acc=model:add=off:aer=off:afr=on:afp=4000:afq=1.4:anc=none:urr=on:updr=off:uhcvi=on_60"); // ISA 31 (4)
  sched.push("dis-11_3_cond=on:fsr=off:gs=on:gsem=on:lcm=reverse:lwlo=on:nwc=1:sd=2:ss=axioms:sos=on:av=off_60"); // ISA 32 (4)
  sched.push("lrs+10_4:1_bd=off:ccuc=small_ones:gs=on:nwc=1:stl=300:sd=2:ss=priority:sos=all:sac=on:acc=model:add=off:afr=on:afp=40000:afq=1.1:amm=off:anc=none_60"); // ISA 33 (4)
  sched.push("dis+11_5_br=off:ccuc=small_ones:cond=fast:fsr=off:gs=on:nwc=1:sd=1:ss=axioms:st=1.2:sos=on:acc=on:add=large:afp=100000:afq=1.2:amm=off:anc=none:sp=reverse_arity:urr=on:updr=off_60"); // ISA 34 (4)
  sched.push("ott+1_8:1_bd=off:br=off:cond=on:nm=64:nwc=1.2:sd=2:ss=priority:st=2.0:av=off:sp=occurrence:urr=on_60"); // ISA 35 (4)
  sched.push("dis+10_2:1_fde=none:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.1:sd=1:ss=axioms:st=3.0:sos=on:sac=on:acc=on:afr=on:afp=100000:afq=1.1:amm=sco:anc=none:sp=reverse_arity:uhcvi=on_60"); // ISA 36 (4)
  sched.push("dis+10_4_cond=on:fsr=off:fde=unused:gs=on:gsem=off:gsssp=full:lcm=reverse:nm=1024:nwc=1:sd=2:ss=priority:sac=on:aer=off:afr=on:afp=4000:afq=1.1:anc=all:updr=off_60"); // ISA 37 (3)
  sched.push("lrs+11_6_cond=fast:fsr=off:fde=unused:gs=on:gsssp=full:nwc=1.1:stl=300:sd=1:ss=axioms:st=5.0:sos=on:sac=on:afp=4000:afq=1.4:amm=off:anc=none:sp=occurrence:urr=on_60"); // ISA 38 (3)
  sched.push("dis-4_3:1_ep=RST:nwc=1:sos=on:av=off:updr=off:uhcvi=on_60"); // ISA 39 (3)
  sched.push("lrs+1003_3_cond=fast:fde=unused:gs=on:gsaa=from_current:nwc=1:stl=300:sd=1:ss=axioms:sos=on:sac=on:add=off:afr=on:afp=1000:afq=1.4:anc=none:sp=reverse_arity:updr=off:uhcvi=on_60"); // ISA 40 (3)
  sched.push("dis-11_3:1_bd=off:fsr=off:fde=unused:lcm=reverse:nm=64:nwc=2.5:sd=5:ss=priority:st=3.0:av=off_60"); // ISA 41 (3)
  sched.push("dis+10_2_cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nwc=1.1:sd=1:ss=axioms:st=5.0:sos=on:av=off_60"); // ISA 42 (3)
  sched.push("dis+1011_1_fsr=off:fde=unused:nm=64:nwc=1.7:sd=2:ss=priority:av=off:updr=off_60"); // ISA 43 (3)
  sched.push("lrs+2_4_bd=off:cond=on:lcm=predicate:nwc=1:stl=300:sd=3:ss=priority:sos=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:urr=ec_only_60"); // ISA 44 (3)
  sched.push("dis+10_2_bd=off:fsr=off:fde=none:gs=on:gsem=on:lcm=reverse:nm=64:nwc=1:sd=3:ss=axioms:st=5.0:sos=on:sac=on:afp=10000:afq=1.4:anc=none:updr=off:uhcvi=on_60"); // ISA 45 (3)
  sched.push("dis+1002_32_bs=on:fde=none:nm=64:nwc=1:sd=2:ss=axioms:st=3.0:sos=on:sac=on:acc=model:add=large:aer=off:afr=on:afp=10000:afq=1.2:anc=none_60"); // ISA 46 (3)
  sched.push("dis+1003_3_cond=on:ep=RST:fde=none:gs=on:gsem=off:lwlo=on:nwc=1:sd=2:ss=axioms:st=1.5:sos=on:sac=on:aer=off:afr=on:afp=1000:afq=1.0:anc=none:updr=off_60"); // ISA 47 (2)
  sched.push("dis+11_24_br=off:cond=fast:ep=RST:fsr=off:fde=none:gsp=on:gs=on:gsaa=full_model:gsem=off:nwc=1.1:sd=1:ss=axioms:sac=on:add=off:afr=on:afp=4000:afq=2.0:amm=sco:anc=none:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // ISA 48 (2)
  sched.push("dis+3_1_cond=on:fde=unused:nwc=1:sd=1:ss=axioms:st=1.2:sos=on:sac=on:add=off:afp=40000:afq=1.4:anc=none_60"); // ISA 49 (2)
  sched.push("dis+10_3_bd=off:fsr=off:gs=on:gsaa=full_model:gsssp=full:lcm=reverse:nwc=1:sd=2:ss=axioms:st=5.0:sos=on:sac=on:add=large:afr=on:afp=10000:afq=1.4:anc=none:sp=occurrence_60"); // ISA 50 (2)
  sched.push("dis+10_2_bd=off:fde=unused:nwc=1:sd=2:ss=axioms:st=2.0:sos=on:av=off:uhcvi=on_60"); // ISA 51 (2)
  sched.push("lrs+11_12_bd=off:bs=unit_only:ccuc=small_ones:cond=fast:fde=none:nwc=2.5:stl=300:sd=5:ss=priority:st=1.2:sos=all:acc=model:aer=off:afp=100000:afq=1.4:anc=none_60"); // ISA 52 (2)
  sched.push("dis+11_3_br=off:ccuc=small_ones:cond=fast:gsp=on:gs=on:gsem=on:nwc=1:sd=3:ss=axioms:st=1.5:sos=all:acc=on:afr=on:afp=1000:afq=2.0:amm=off:anc=none:sp=reverse_arity:urr=on:updr=off_60"); // ISA 53 (2)
  sched.push("ott+1011_10_fsr=off:fde=unused:nm=0:nwc=1:sd=3:ss=priority:st=1.2:av=off:uhcvi=on_60"); // ISA 55 (2)
  sched.push("ott+11_5:1_bd=off:cond=fast:nm=64:nwc=1.1:sd=3:ss=priority:st=2.0:av=off:sp=reverse_arity:urr=on:updr=off_60"); // ISA 56 (2)
  sched.push("lrs-3_3:1_cond=fast:ep=R:gsp=on:gs=on:gsem=on:gsssp=full:lcm=predicate:nwc=1:stl=300:sd=1:ss=axioms:st=3.0:sac=on:add=off:afr=on:afp=40000:afq=1.1:amm=sco:anc=none:uhcvi=on_60"); // ISA 57 (1)
  sched.push("dis+1011_2_cond=fast:ep=RST:fsr=off:fde=none:gs=on:gsem=off:gsssp=full:nwc=4:sd=2:ss=priority:sac=on:add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:sp=reverse_arity_60"); // ISA 58 (1)
  sched.push("dis+1002_4_cond=on:fde=none:gs=on:gsem=on:nwc=1:sd=4:ss=axioms:sos=on:av=off:sp=occurrence:uhcvi=on_60"); // ISA 59 (1)
  sched.push("dis-1_4_cond=fast:fsr=off:gs=on:gsem=off:gsssp=full:lcm=reverse:nwc=1:sd=1:ss=axioms:st=1.5:sos=on:av=off:updr=off:uhcvi=on_60"); // ISA 60 (1)
  sched.push("dis+10_4:1_fsr=off:gs=on:gsem=on:lcm=reverse:nm=64:nwc=1:sd=4:ss=priority:st=3.0:av=off:updr=off:uhcvi=on_60"); // ISA 61 (1)
  sched.push("dis+10_2_fsr=off:fde=none:lcm=reverse:lwlo=on:nm=64:nwc=1.2:sd=4:ss=priority:st=5.0:av=off:uhcvi=on_60"); // ISA 62 (1)
  sched.push("lrs+10_4_bd=off:cond=on:fde=unused:gs=on:gsem=off:lcm=predicate:nwc=1:stl=300:sd=2:ss=axioms:st=5.0:sos=on:av=off:urr=ec_only_60"); // ISA 63 (1)
  sched.push("dis+10_3_ep=RST:fde=unused:gs=on:gsem=off:nwc=1:sos=on:afp=100000:afq=1.1:amm=sco:anc=none:sp=occurrence:updr=off_60"); // ISA 65 (1)
  sched.push("dis+10_4_cond=fast:fsr=off:fde=unused:gs=on:gsaa=full_model:gsem=off:nwc=1.5:sd=1:ss=axioms:st=3.0:sac=on:add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:sp=reverse_arity:updr=off:uhcvi=on_60"); // ISA 66 (1)
  sched.push("ott+10_8_cond=on:gs=on:gsem=off:nm=64:nwc=1:sd=1:ss=axioms:st=3.0:sos=all:av=off:sp=reverse_arity:urr=on:updr=off_60"); // ISA 67 (1)
  sched.push("dis+1003_2:1_cond=fast:fde=none:nwc=1:sd=1:ss=axioms:st=2.0:sos=all:av=off:sp=reverse_arity:urr=ec_only_60"); // ISA 68 (1)
  sched.push("lrs+10_3_bd=off:cond=on:gs=on:gsem=off:nwc=1:stl=300:sd=3:ss=priority:st=3.0:sos=all:av=off:uhcvi=on_60"); // ISA 69 (1)
  sched.push("lrs+10_3_bd=off:cond=fast:fde=unused:lcm=reverse:nwc=1:stl=300:sd=5:ss=axioms:st=1.5:sos=on:av=off:sp=occurrence:urr=ec_only_60"); // ISA 70 (1)
  sched.push("dis+1011_4_cond=fast:ep=RST:fsr=off:gs=on:nm=64:nwc=1:sd=3:ss=axioms:st=3.0:sos=on:av=off_60"); // ISA 71 (1)
  sched.push("dis+11_1_cond=fast:gsp=on:lcm=predicate:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:av=off:sp=occurrence:uhcvi=on_60"); // ISA 72 (1)
  sched.push("dis-11_4_bd=off:fde=none:gs=on:gsem=on:lwlo=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:av=off:sp=reverse_arity:urr=on:updr=off_60"); // ISA 73 (1)
  sched.push("dis+10_1_cond=fast:ep=RST:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=on:gsssp=full:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on:add=off:afr=on:afp=40000:afq=2.0:anc=none:sp=occurrence:urr=ec_only_60"); // ISA 74 (1)
  sched.push("lrs+11_40_bs=unit_only:cond=fast:gs=on:gsem=on:gsssp=full:lcm=reverse:nm=64:nwc=1.3:stl=300:sd=3:ss=priority:av=off:sp=reverse_arity:updr=off_60"); // ISA 75 (1)
  sched.push("dis+1002_7_gs=on:gsaa=from_current:gsem=on:nm=64:nwc=1:sd=2:ss=axioms:st=1.5:sos=on:sac=on:add=large:afr=on:afp=40000:afq=1.0:amm=off:anc=none_60"); // ISA 76 (1)
  sched.push("lrs+11_1_cond=fast:ep=RST:lwlo=on:nwc=1:stl=300:sd=2:ss=axioms:sos=all:av=off:sp=occurrence:uhcvi=on_60"); // ISA 77 (1)
  sched.push("lrs+11_4_bd=off:br=off:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=off:gsssp=full:nwc=1:stl=300:sd=2:ss=axioms:st=5.0:sos=all:sac=on:add=large:aer=off:afp=1000:afq=1.4:anc=none:sp=occurrence:urr=on:uhcvi=on_60"); // ISA 78 (1)
  sched.push("lrs+1010_8:1_bs=unit_only:cond=fast:fsr=off:fde=unused:gs=on:gsaa=full_model:gsem=off:lwlo=on:nwc=4:stl=300:sd=3:ss=priority:st=2.0:sac=on:aac=none:add=off:aer=off:afp=1000:afq=2.0:sp=occurrence:urr=ec_only:uhcvi=on_60"); // ISA 79 (1)
  sched.push("lrs+1011_4_ep=RST:fsr=off:gs=on:gsssp=full:nwc=1.1:stl=300:sos=on:av=off:updr=off_60"); // ISA 80 (1)
  sched.push("lrs+11_24_bd=off:bsr=unit_only:cond=on:gs=on:gsssp=full:nm=0:nwc=1.1:stl=300:sd=1:ss=axioms:st=3.0:sos=all:av=off:sp=occurrence:urr=ec_only_60"); // ISA 81 (1)
}

// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------


void Schedules::getLtb2017HllSchedule(const Property& property, Schedule& sched) {
  sched.push("lrs-4_5:4_bd=off:bs=unit_only:bsr=on:cond=on:fde=none:gs=on:gsaa=full_model:gsem=off:nm=0:nwc=1.1:nicw=on:stl=300:sd=1:ss=axioms:st=2.0:sos=on:sac=on:afr=on:afp=10000:afq=1.0:amm=off:anc=none:sp=reverse_arity:urr=on:updr=off_60"); // HLL 2 (382)
  sched.push("dis+1002_1_ep=RST:gs=on:gsaa=full_model:gsem=on:nm=64:nwc=1:sd=7:ss=axioms:st=1.2:sos=on:aer=off:afp=40000:afq=1.2:anc=none:updr=off:uhcvi=on_60"); // HLL 3 (170)
  sched.push("dis+1002_1_gs=on:gsem=off:nwc=1:sd=3:ss=axioms:sos=on:sac=on:afp=1000:afq=1.4:amm=sco:anc=none:sp=reverse_arity:urr=on_60"); // HLL 4 (148)
  sched.push("lrs+1011_4:1_bd=off:bsr=unit_only:ccuc=small_ones:fsr=off:fde=unused:gs=on:gsssp=full:nm=64:nwc=4:stl=300:sd=1:ss=priority:sac=on:acc=model:add=large:aer=off:afr=on:afp=100000:afq=1.2:anc=all:uhcvi=on_60"); // HLL 5 (68)
  sched.push("lrs+10_1_bsr=unit_only:cond=fast:gs=on:gsem=off:gsssp=full:lcm=reverse:nwc=1:stl=300:sd=2:ss=axioms:st=5.0:sos=on:sac=on:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:sp=reverse_arity:urr=on:updr=off_60"); // HLL 7 (62)
  sched.push("dis+10_3:1_ep=RST:gsp=on:gs=on:gsem=on:lcm=reverse:nwc=1.1:sd=2:ss=priority:st=2.0:sos=on:sac=on:add=large:aer=off:afp=10000:afq=1.1:anc=none:sp=reverse_arity_60"); // HLL 8 (42)
  sched.push("lrs+1011_3:1_bd=off:bsr=on:cond=fast:gs=on:gsem=on:lwlo=on:nwc=10:stl=300:sd=1:ss=axioms:st=3.0:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // HLL 9 (35)
  sched.push("lrs+1011_5:1_fde=none:gs=on:gsem=on:nwc=4:stl=300:sd=1:ss=axioms:st=5.0:av=off:sp=occurrence:urr=on:uhcvi=on_60"); // HLL 10 (25)
  sched.push("ott+11_2:3_cond=on:ep=RST:fsr=off:fde=none:gsp=on:lcm=predicate:nwc=1:sd=3:ss=priority:sos=all:sac=on:aac=none:aer=off:afp=100000:afq=1.2:anc=all_dependent:urr=ec_only_60"); // HLL 12 (21)
  sched.push("dis+1011_5:1_ep=RSTC:fde=unused:gs=on:gsssp=full:lwlo=on:nm=0:nwc=1:sd=1:ss=axioms:st=3.0:sos=on:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // HLL 13 (16)
  sched.push("dis+1011_5:1_cond=fast:fsr=off:fde=none:gs=on:gsaa=from_current:nwc=3:sd=2:ss=axioms:sac=on:afp=100000:afq=1.0:amm=sco:anc=none:sp=reverse_arity:urr=on:updr=off_60"); // HLL 14 (14)
  sched.push("lrs+11_3_cond=fast:gsp=on:gs=on:gsem=on:gsssp=full:lcm=predicate:nwc=1:stl=300:sd=2:ss=axioms:sos=on:sac=on:add=large:afr=on:afp=100000:afq=1.0:amm=sco:anc=none:updr=off:uhcvi=on_60"); // HLL 15 (14)
  sched.push("dis+1011_2:1_cond=fast:ep=RST:fsr=off:gs=on:gsem=off:gsssp=full:nwc=1:sd=1:ss=axioms:sos=on:add=large:aer=off:afr=on:afp=4000:afq=1.1:anc=none:sp=reverse_arity_60"); // HLL 16 (13)
  sched.push("dis+1011_1_cond=fast:ep=RST:gs=on:nwc=1:sd=2:ss=axioms:st=1.5:sos=on:sac=on:amm=sco:anc=none:urr=ec_only_60"); // HLL 17 (12)
  sched.push("lrs+10_4_bd=off:bsr=unit_only:fde=none:gs=on:lcm=reverse:nwc=1:stl=300:sd=3:ss=axioms:st=3.0:sos=on:av=off:uhcvi=on_60"); // HLL 18 (11)
  sched.push("dis+1002_7_bsr=unit_only:cond=fast:nm=64:nwc=1:sd=1:ss=axioms:sos=on:sac=on:afr=on:afp=100000:afq=1.4:anc=none:uhcvi=on_60"); // HLL 19 (11)
  sched.push("lrs+10_5_bd=off:cond=fast:fde=unused:gsp=on:gs=on:gsem=on:gsssp=full:nwc=1:stl=300:sd=2:ss=axioms:sos=on:av=off:urr=on:updr=off:uhcvi=on_60"); // HLL 20 (10)
  sched.push("dis+2_4_bd=off:cond=fast:fsr=off:fde=none:gs=on:gsem=on:lcm=reverse:lwlo=on:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:av=off:sp=occurrence:uhcvi=on_60"); // HLL 21 (9)
  sched.push("lrs+1010_5:1_bs=unit_only:bsr=on:fde=none:gs=on:gsem=off:gsssp=full:lcm=reverse:nm=0:nwc=4:stl=300:sd=3:ss=priority:st=1.2:sos=on:aac=none:acc=model:afr=on:afp=1000:afq=1.0:amm=off:urr=on:uhcvi=on_60"); // HLL 22 (8)
  sched.push("lrs-11_8:1_bsr=on:cond=on:fde=none:lcm=reverse:nm=0:nwc=1.5:stl=300:sd=2:ss=priority:av=off:sp=occurrence_60"); // HLL 23 (7)
  sched.push("dis+1002_3_cond=on:ep=RS:fsr=off:gs=on:gsaa=full_model:gsem=off:nm=0:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:afp=4000:afq=1.4:amm=off:anc=none:updr=off_60"); // HLL 24 (7)
  sched.push("dis+1003_5_cond=on:fsr=off:fde=none:gs=on:gsem=off:nwc=1:sos=on:add=large:aer=off:afr=on:afp=100000:afq=1.0:anc=all_dependent:sp=reverse_arity:urr=ec_only:uhcvi=on_60"); // HLL 25 (6)
  sched.push("lrs+10_5:4_bd=off:gs=on:gsssp=full:lcm=reverse:nwc=1:stl=300:sd=1:ss=axioms:sos=on:sac=on:add=off:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:sp=reverse_arity:updr=off:uhcvi=on_60"); // HLL 26 (6)
  sched.push("lrs+11_4:1_br=off:cond=on:fsr=off:fde=unused:gsp=on:gs=on:gsssp=full:lcm=predicate:nm=0:nwc=1:stl=300:sd=1:ss=axioms:av=off:sp=occurrence:urr=on_60"); // HLL 27 (6)
  sched.push("lrs+1010_5_cond=fast:ep=RST:gs=on:gsaa=from_current:gsem=on:nwc=1:stl=300:sd=4:ss=axioms:st=1.5:sos=on:sac=on:add=off:afp=4000:afq=2.0:amm=sco:anc=none:sp=reverse_arity:uhcvi=on_60"); // HLL 28 (6)
  sched.push("lrs+11_3_bd=off:cond=fast:fde=none:gsp=on:gs=on:gsaa=from_current:gsem=on:gsssp=full:nwc=1:stl=300:sd=1:ss=axioms:sos=all:add=large:aer=off:afr=on:afp=4000:afq=2.0:anc=none:sp=occurrence:urr=on:updr=off_60"); // HLL 29 (5)
  sched.push("lrs+4_5:4_bd=off:bs=on:bsr=unit_only:cond=fast:fde=unused:gs=on:gsem=off:nwc=1:stl=300:sd=2:ss=axioms:st=2.0:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // HLL 30 (5)
  sched.push("lrs+11_5:1_bd=off:br=off:cond=fast:gsp=on:gs=on:gsem=on:gsssp=full:lcm=predicate:nwc=1.1:stl=300:sd=2:ss=priority:st=3.0:av=off:sp=occurrence:urr=on:uhcvi=on_60"); // HLL 31 (5)
  sched.push("dis+1011_3:2_cond=fast:ep=RST:fsr=off:fde=unused:gsp=on:gs=on:gsem=off:nm=0:nwc=1:sd=1:ss=priority:sos=all:add=large:anc=all:sp=occurrence_60"); // HLL 32 (5)
  sched.push("lrs+11_3:1_br=off:cond=fast:ep=R:fsr=off:gs=on:nwc=1:stl=300:sd=2:ss=priority:st=2.0:sos=all:av=off:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // HLL 33 (4)
  sched.push("lrs+11_3_bsr=unit_only:cond=on:ep=RST:gsp=on:nwc=1.7:stl=300:sd=3:ss=axioms:st=5.0:sos=all:sac=on:afr=on:afp=100000:afq=1.1:anc=all_dependent:sp=reverse_arity:updr=off:uhcvi=on_60"); // HLL 34 (4)
  sched.push("dis+1010_2:3_bs=unit_only:bsr=unit_only:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:gsssp=full:nm=0:nwc=3:sd=4:ss=priority:st=1.5:sos=on:acc=on:add=off:aer=off:afr=on:afp=100000:afq=1.0:sp=reverse_arity:uhcvi=on_60"); // HLL 36 (3)
  sched.push("dis+1010_5:4_bd=off:fsr=off:fde=unused:gs=on:nm=64:nwc=1:sd=4:ss=axioms:st=1.2:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // HLL 37 (3)
  sched.push("lrs+1011_8:1_bd=off:bsr=unit_only:fde=none:gs=on:lwlo=on:nm=0:nwc=1.5:stl=300:sd=1:ss=axioms:st=1.2:av=off:sp=occurrence:updr=off_60"); // HLL 38 (3)
  sched.push("dis+4_5:4_bd=off:fsr=off:fde=unused:gs=on:nwc=1:sd=5:ss=axioms:st=1.5:sos=all:av=off:sp=occurrence:uhcvi=on_60"); // HLL 39 (3)
  sched.push("dis+1011_3_cond=fast:ep=R:gs=on:gsem=off:lwlo=on:nm=0:nwc=1:sd=5:ss=axioms:st=1.5:sos=on:sac=on:add=large:afr=on:afp=1000:afq=1.1:anc=none:uhcvi=on_60"); // HLL 40 (2)
  sched.push("lrs+1004_3:1_bd=off:bsr=unit_only:cond=fast:fde=none:gs=on:gsem=off:gsssp=full:nwc=1:stl=300:sd=2:ss=axioms:sos=on:av=off:updr=off_60"); // HLL 41 (2)
  sched.push("lrs+10_1_bd=off:bsr=unit_only:cond=fast:fsr=off:fde=unused:gs=on:gsem=off:lcm=reverse:nwc=1:stl=300:sd=3:ss=axioms:st=1.5:av=off:sp=reverse_arity:urr=on_60"); // HLL 42 (2)
  sched.push("lrs+10_4_bd=off:bsr=unit_only:cond=on:gs=on:nwc=1:stl=300:sd=4:ss=axioms:st=5.0:sos=all:av=off:sp=reverse_arity:updr=off:uhcvi=on_60"); // HLL 43 (2)
  sched.push("lrs+1010_2:3_bsr=unit_only:ccuc=small_ones:cond=on:fde=unused:gs=on:gsaa=full_model:nwc=1:stl=300:sd=2:ss=axioms:st=1.5:sos=on:sac=on:acc=model:add=off:aer=off:afr=on:afp=1000:afq=2.0:sp=occurrence:uhcvi=on_60"); // HLL 45 (2)
  sched.push("dis+10_1_bd=preordered:bs=unit_only:cond=on:fde=none:lcm=predicate:nwc=1:sd=2:ss=axioms:sos=all:sac=on:afr=on:amm=sco:anc=none:updr=off:uhcvi=on_60"); // HLL 46 (2)
  sched.push("lrs+11_5_bd=off:bsr=unit_only:cond=on:fsr=off:gs=on:gsaa=from_current:gsssp=full:nwc=1:stl=300:sd=1:ss=axioms:st=5.0:sos=all:add=off:afp=4000:afq=2.0:amm=off:anc=none:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // HLL 47 (2)
  sched.push("dis+11_2:1_br=off:ep=RST:fde=unused:gsp=on:gs=on:gsaa=from_current:gsem=off:nwc=1:sd=1:ss=priority:st=1.2:sos=all:add=large:aer=off:afp=100000:afq=1.1:anc=none:sp=occurrence:urr=on_60"); // HLL 48 (2)
  sched.push("dis+1011_2:3_cond=fast:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:gsssp=full:nm=0:nwc=1:sd=2:ss=axioms:sos=on:sac=on:add=large:afr=on:afp=1000:afq=2.0:anc=none:sp=reverse_arity:urr=ec_only:uhcvi=on_60"); // HLL 49 (2)
  sched.push("lrs+1003_4_bsr=unit_only:cond=fast:fsr=off:gsp=on:gs=on:gsaa=from_current:nm=0:nwc=1:stl=300:sos=on:sac=on:add=large:afp=10000:afq=1.1:anc=none:urr=ec_only:uhcvi=on_60"); // HLL 50 (1)
  sched.push("dis+11_20_cond=fast:ep=R:fde=none:lwlo=on:nm=0:nwc=10:sd=4:ss=axioms:st=2.0:add=large:amm=off:sp=occurrence_60"); // HLL 52 (1)
  sched.push("lrs-2_3_bd=off:bs=unit_only:cond=on:fde=none:nwc=1:stl=300:sd=1:ss=axioms:st=1.2:sos=all:av=off:sp=occurrence:urr=ec_only:updr=off_60"); // HLL 53 (1)
  sched.push("lrs+11_3_bsr=unit_only:cond=on:ep=RST:fsr=off:fde=none:gs=on:gsem=off:gsssp=full:nwc=1:stl=300:sd=10:ss=axioms:st=1.5:sos=all:add=off:afp=40000:afq=1.0:anc=none:sp=occurrence:urr=on_60"); // HLL 54 (1)
  sched.push("lrs+1004_4_cond=on:fde=unused:gsp=on:gs=on:nwc=1:stl=300:sd=3:ss=axioms:st=5.0:sos=on:av=off:sp=occurrence:urr=on:updr=off_60"); // HLL 55 (1)
  sched.push("lrs+10_4_bsr=unit_only:cond=fast:fsr=off:fde=unused:gs=on:gsssp=full:nwc=1:stl=300:sd=2:ss=axioms:st=2.0:sos=on:afp=10000:afq=1.0:amm=sco:anc=all_dependent:sp=occurrence:uhcvi=on_60"); // HLL 56 (1)
  sched.push("dis+1011_3:1_cond=fast:fsr=off:fde=unused:lwlo=on:nwc=1:sd=2:ss=axioms:st=1.2:av=off:sp=reverse_arity:uhcvi=on_60"); // HLL 57 (1)
  sched.push("lrs-10_3:1_cond=fast:fde=unused:gs=on:gsaa=from_current:gsem=off:lcm=predicate:nwc=1:stl=300:sd=1:ss=axioms:sos=on:sac=on:add=off:afp=100000:afq=2.0:amm=sco:anc=none:sp=reverse_arity:uhcvi=on_60"); // HLL 58 (1)
  sched.push("lrs-10_3:1_bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=off:gsssp=full:lcm=reverse:nm=0:nwc=1:stl=300:sd=4:ss=axioms:st=1.5:sos=on:av=off:urr=ec_only:updr=off_60"); // HLL 59 (1)
  sched.push("lrs+4_5_bd=off:fde=none:nwc=1.1:stl=300:sd=2:ss=axioms:st=5.0:sos=on:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // HLL 61 (1)
  sched.push("lrs-2_5:4_bd=off:bsr=unit_only:fsr=off:nm=0:nwc=1:stl=300:sd=2:ss=axioms:sos=on:av=off:sp=reverse_arity_60"); // HLL 62 (1)
  sched.push("lrs+11_5_bd=off:fde=none:gsp=on:gs=on:gsaa=full_model:gsssp=full:nwc=1:stl=300:sd=2:ss=priority:st=2.0:sos=all:sac=on:add=large:aer=off:afp=40000:afq=1.2:anc=none:uhcvi=on_60"); // HLL 63 (1)
  sched.push("lrs+11_24_bsr=unit_only:gsp=on:gs=on:gsem=off:gsssp=full:nm=0:nwc=1:stl=300:sd=2:ss=axioms:sos=all:sac=on:afp=1000:afq=1.0:amm=sco:anc=none:sp=reverse_arity:updr=off_60"); // HLL 64 (1)
  sched.push("dis+11_2_bd=off:cond=fast:gs=on:gsaa=full_model:nwc=1:sd=7:ss=axioms:st=1.2:sos=all:sac=on:add=off:afr=on:afp=40000:afq=1.2:anc=all_dependent_60"); // HLL 66 (1)
  sched.push("lrs+1004_2:3_bd=off:ccuc=small_ones:cond=fast:fsr=off:fde=none:lwlo=on:nm=0:nwc=1.5:stl=300:sac=on:aac=none:acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:sp=reverse_arity_60"); // HLL 67 (1)
  sched.push("dis+11_1_cond=fast:fde=none:gs=on:gsssp=full:nwc=1.1:sd=1:ss=axioms:sac=on:add=large:afp=1000:afq=2.0:amm=sco:anc=none:urr=on:updr=off:uhcvi=on_60"); // HLL 68 (1)
  sched.push("dis+2_5_bd=off:cond=fast:gs=on:lcm=reverse:nwc=1:sd=3:ss=axioms:sos=on:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // HLL 69 (1)
  sched.push("lrs+4_3_bsr=unit_only:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=off:gsssp=full:nwc=1:stl=300:sd=1:ss=axioms:st=1.5:sos=on:sac=on:add=off:afr=on:afp=100000:afq=1.0:amm=sco:anc=none:sp=reverse_arity:urr=on:updr=off:uhcvi=on_60"); // HLL 70 (1)
  sched.push("lrs+11_2:3_bd=off:cond=on:fde=none:nwc=1:stl=300:sd=10:ss=axioms:st=1.2:sos=all:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // HLL 71 (1)
  sched.push("dis+11_4_cond=on:ep=RST:fsr=off:fde=unused:gs=on:gsaa=from_current:nwc=1:sd=2:ss=axioms:sos=all:add=off:aer=off:anc=none:sp=occurrence:uhcvi=on_60"); // HLL 72 (1)
  sched.push("lrs+1003_3_bd=off:bsr=unit_only:cond=on:nwc=1:stl=300:sd=2:ss=priority:av=off_60"); // HLL 73 (1)
}

// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------

void Schedules::getLtb2017MzrSchedule(const Property& property, Schedule& sched) {
  sched.push("ott-11_8:1_bsr=unit_only:lcm=predicate:nwc=1:sd=2:ss=axioms:st=1.2:sos=all:av=off:sp=reverse_arity_60"); // MZR 1 (828)
  sched.push("ott+1010_3:1_bs=unit_only:bsr=unit_only:br=off:ccuc=first:cond=fast:fde=unused:gs=on:gsem=on:nwc=1:sd=2:ss=axioms:sos=on:sac=on:aac=none:acc=on:aer=off:afp=1000:afq=2.0:anc=all_dependent:sp=reverse_arity:urr=on:updr=off_60"); // MZR 2 (112)
  sched.push("lrs+1004_2_bd=off:ccuc=small_ones:gs=on:gsem=off:gsssp=full:lwlo=on:nm=0:nwc=1:stl=300:sd=4:ss=priority:st=5.0:sos=all:sac=on:acc=on:add=off:aer=off:afp=100000:afq=1.2:anc=none:sp=occurrence:updr=off:uhcvi=on_60"); // MZR 4 (47)
  sched.push("dis+10_5_bsr=unit_only:cond=on:ep=RS:fde=unused:nm=0:nwc=1:sd=1:ss=axioms:sos=all:av=off_60"); // MZR 5 (37)
  sched.push("lrs+11_5:1_br=off:cond=fast:fde=unused:gsp=on:gs=on:gsem=on:gsssp=full:lcm=predicate:nm=0:nwc=1:nicw=on:stl=300:sd=1:ss=axioms:st=1.2:sac=on:add=large:afr=on:afp=40000:afq=1.4:amm=sco:anc=all:urr=on_60"); // MZR 6 (32)
  sched.push("lrs+1011_8:1_cond=on:fde=none:gsp=on:lwlo=on:nwc=1:stl=300:sd=2:ss=axioms:sos=all:av=off:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_60"); // MZR 7 (22)
  sched.push("lrs+11_3_br=off:cond=fast:gs=on:gsem=off:nwc=1:stl=300:sd=3:ss=priority:st=1.5:sos=all:sac=on:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:sp=occurrence:urr=on:uhcvi=on_60"); // MZR 8 (21)
  sched.push("dis+10_2:1_cond=fast:ep=RST:fsr=off:fde=unused:gsp=on:gs=on:gsaa=full_model:gsem=off:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=on:sac=on:add=off:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:urr=on:updr=off:uhcvi=on_60"); // MZR 9 (19)
  sched.push("lrs+1002_1_bsr=unit_only:nwc=1:stl=300:sd=1:ss=axioms:st=1.5:sos=all:av=off:updr=off:uhcvi=on_60"); // MZR 10 (14)
  sched.push("lrs+1_1_bs=on:bsr=on:br=off:cond=fast:fsr=off:gs=on:gsem=off:lwlo=on:nwc=3:stl=300:sd=3:ss=priority:add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:sp=occurrence:urr=on:updr=off_60"); // MZR 11 (11)
  sched.push("lrs-2_1_cond=on:fde=unused:gs=on:gsaa=from_current:gsssp=full:lcm=predicate:nwc=1:stl=300:sd=4:ss=axioms:st=3.0:sos=on:sac=on:afr=on:afp=10000:afq=1.1:anc=none:updr=off_60"); // MZR 12 (11)
  sched.push("lrs+10_8:1_bsr=unit_only:br=off:cond=on:fsr=off:gsp=on:gs=on:gsaa=from_current:nm=0:nwc=1:stl=300:sd=2:ss=axioms:st=1.2:sos=on:sac=on:add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:sp=reverse_arity:urr=on:updr=off:uhcvi=on_60"); // MZR 13 (10)
  sched.push("dis+11_12_cond=fast:nwc=1:sd=1:ss=axioms:st=1.5:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // MZR 14 (8)
  sched.push("dis+1010_3_bsr=unit_only:cond=fast:fde=none:nwc=1:sd=2:ss=axioms:st=1.5:sos=all:av=off:sp=occurrence:uhcvi=on_60"); // MZR 15 (8)
  sched.push("dis+1002_2:3_fde=none:gsp=on:nm=0:nwc=1:sd=3:ss=axioms:sos=on:sac=on:afp=100000:afq=1.0:amm=sco:anc=none:sp=occurrence:updr=off_60"); // MZR 16 (7)
  sched.push("lrs+10_3:1_fde=unused:lcm=reverse:nwc=1:stl=300:sd=3:ss=priority:st=2.0:sos=all:av=off:sp=occurrence:uhcvi=on_60"); // MZR 17 (6)
  sched.push("lrs+10_2:3_bsr=unit_only:cond=on:fde=none:gs=on:nwc=1:stl=300:sd=2:ss=axioms:sos=on:av=off:sp=reverse_arity_60"); // MZR 18 (6)
  sched.push("dis+1004_3:1_bsr=unit_only:ep=R:fde=unused:gs=on:gsssp=full:nm=0:nwc=1:sos=all:sac=on:afr=on:afp=10000:afq=2.0:anc=all:sp=reverse_arity:urr=on:updr=off_60"); // MZR 19 (5)
  sched.push("ott+4_5:1_br=off:cond=fast:fsr=off:nwc=1.3:av=off:sp=occurrence:urr=on:uhcvi=on_60"); // MZR 20 (5)
  sched.push("dis+1010_1_cond=fast:fsr=off:nwc=1.3:sd=2:ss=axioms:st=1.5:sos=on:acc=model:add=off:afp=4000:afq=2.0:uhcvi=on_60"); // MZR 21 (5)
  sched.push("lrs+11_2_bd=off:bsr=unit_only:cond=on:lcm=predicate:lwlo=on:nm=64:nwc=1.1:stl=300:sd=1:ss=axioms:st=2.0:sos=all:av=off_60"); // MZR 22 (5)
  sched.push("lrs+10_4:1_bd=off:cond=fast:fde=unused:lcm=reverse:nm=0:nwc=1.2:stl=300:sd=2:ss=axioms:sos=all:av=off_60"); // MZR 23 (5)
  sched.push("dis+10_5_ep=RST:fsr=off:gs=on:gsssp=full:lwlo=on:nm=0:nwc=1:sd=4:ss=axioms:sos=on:afr=on:afp=40000:afq=1.1:amm=off:anc=none:uhcvi=on_60"); // MZR 24 (4)
  sched.push("dis+1002_3_ep=RST:fde=unused:gs=on:gsaa=full_model:gsem=off:nwc=1:sd=1:ss=axioms:st=2.0:sos=on:afp=100000:afq=1.1:anc=none:sp=occurrence:uhcvi=on_60"); // MZR 25 (4)
  sched.push("dis+10_5_cond=on:fsr=off:fde=none:gs=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=on:av=off_60"); // MZR 26 (4)
  sched.push("ott-11_8:1_bd=preordered:ccuc=first:er=known:fsr=off:fde=unused:gsp=on:lcm=predicate:nm=0:nwc=2:sd=3:ss=axioms:acc=on:afp=10000:afq=2.0:amm=sco:sp=occurrence:updr=off_60"); // MZR 27 (4)
  sched.push("lrs+1011_1_cond=on:fsr=off:gs=on:nwc=1:stl=300:sd=4:ss=priority:st=1.2:sos=on:av=off:sp=reverse_arity:urr=on_60"); // MZR 29 (3)
  sched.push("lrs+11_3:1_bsr=unit_only:br=off:cond=on:ep=RST:fsr=off:gs=on:gsaa=from_current:gsem=off:nwc=3:stl=300:sd=2:ss=axioms:st=2.0:sac=on:add=large:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:sp=reverse_arity:urr=on_60"); // MZR 30 (3)
  sched.push("dis+11_5:4_ccuc=first:cond=on:er=known:fde=none:gs=on:nwc=1:sd=2:ss=priority:st=1.2:sos=all:aac=none:acc=model:add=large:afr=on:afp=10000:afq=1.2:anc=all_dependent:sp=reverse_arity:urr=on:uhcvi=on_60"); // MZR 32 (3)
  sched.push("lrs+1010_2_cond=on:fde=none:gs=on:gsem=off:nwc=1:stl=300:sd=3:ss=priority:st=1.2:sos=all:av=off:uhcvi=on_60"); // MZR 33 (3)
  sched.push("lrs+10_5:4_bd=off:ccuc=small_ones:cond=on:fde=none:gs=on:gsaa=from_current:gsem=off:nm=0:nwc=1:stl=300:sd=2:ss=priority:sos=on:acc=model:add=large:aer=off:afp=100000:afq=1.4:anc=none:urr=on_60"); // MZR 35 (2)
  sched.push("dis+11_1_ccuc=first:cond=on:fsr=off:fde=none:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1:nicw=on:sd=3:ss=priority:acc=model:add=large:afp=4000:afq=1.4:anc=all:sp=occurrence:updr=off:uhcvi=on_60"); // MZR 36 (2)
  sched.push("dis+1_1_fsr=off:gs=on:gsem=on:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:acc=on:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:sp=reverse_arity_60"); // MZR 37 (2)
  sched.push("dis+1004_2_bs=unit_only:bsr=unit_only:fde=unused:gs=on:nwc=1:sos=on:add=large:afr=on_60"); // MZR 38 (2)
  sched.push("dis+11_4_ep=RS:fde=none:gs=on:gsaa=full_model:gsem=off:nwc=1:sd=1:ss=priority:st=1.2:sos=all:sac=on:afp=10000:afq=1.1:amm=sco:anc=none:sp=reverse_arity:uhcvi=on_60"); // MZR 39 (2)
  sched.push("lrs+11_8_br=off:cond=on:fde=none:gs=on:gsem=on:gsssp=full:nwc=1:nicw=on:stl=300:sd=1:ss=axioms:st=5.0:sos=all:sac=on:add=off:afp=100000:afq=1.4:amm=off:anc=all:sp=reverse_arity:urr=on:uhcvi=on_60"); // MZR 40 (2)
  sched.push("ott+1_28_cond=fast:er=filter:fde=none:gsp=on:lcm=reverse:nwc=1.1:sos=on:av=off:sp=reverse_arity:updr=off:uhcvi=on_60"); // MZR 41 (2)
  sched.push("dis+10_14_cond=fast:gs=on:gsaa=full_model:gsem=off:gsssp=full:nwc=1.5:sd=1:ss=axioms:st=1.5:afp=40000:afq=1.1:amm=sco:anc=none:sp=occurrence:updr=off_60"); // MZR 43 (2)
  sched.push("lrs+11_5_fde=none:gsp=on:gs=on:gsem=on:nwc=1:stl=300:sd=3:ss=axioms:st=3.0:sos=on:av=off:sp=occurrence:urr=on_60"); // MZR 45 (2)
  sched.push("lrs-10_4:1_cond=on:fsr=off:fde=unused:gsp=on:gs=on:gsem=on:nwc=1:stl=300:sd=3:ss=axioms:sos=on:av=off:urr=on_60"); // MZR 46 (2)
  sched.push("lrs+3_3:1_bd=preordered:bs=on:bsr=unit_only:fsr=off:fde=unused:gs=on:gsem=off:nwc=1:nicw=on:stl=300:sd=2:ss=axioms:st=3.0:sos=all:sac=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:sp=reverse_arity:urr=ec_only_60"); // MZR 47 (2)
  sched.push("dis+11_3_cond=fast:fsr=off:nwc=1:sd=1:ss=axioms:st=5.0:add=off:afr=on:afp=4000:afq=1.1:anc=none:sp=occurrence:updr=off_60"); // MZR 48 (1)
  sched.push("dis+11_4_bd=off:fsr=off:fde=unused:gs=on:gsaa=full_model:gsem=on:nwc=1:sd=1:ss=axioms:sac=on:add=large:afp=1000:afq=2.0:amm=sco:anc=none:sp=reverse_arity_60"); // MZR 49 (1)
  sched.push("dis+1010_2_bs=on:cond=fast:ep=RSTC:fde=unused:lwlo=on:nwc=1:sos=on:sac=on:add=off:afr=on:afp=10000:afq=1.4:sp=reverse_arity:uhcvi=on_60"); // MZR 50 (1)
  sched.push("dis+10_5_fsr=off:fde=unused:gs=on:gsem=on:gsssp=full:lcm=reverse:nwc=1:sd=2:ss=axioms:sos=on:add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:sp=occurrence:updr=off:uhcvi=on_60"); // MZR 51 (1)
  sched.push("lrs+1_4:1_br=off:cond=on:er=known:fsr=off:fde=unused:gs=on:nm=0:nwc=1:stl=600:sd=1:ss=priority:st=1.5:sos=on:sac=on:add=off:afp=4000:afq=1.1:amm=sco:anc=none:urr=on:updr=off:uhcvi=on_60"); // MZR 52 (1)
  sched.push("dis+1010_5_cond=fast:fde=unused:gs=on:gsem=on:nm=0:nwc=1:sd=2:ss=axioms:st=3.0:sos=on:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // MZR 54 (1)
  sched.push("lrs+11_8:1_bd=off:fde=unused:nwc=1:stl=300:sd=2:ss=axioms:sos=on:av=off:updr=off:uhcvi=on_60"); // MZR 55 (1)
  sched.push("lrs+1003_4_cond=on:fsr=off:fde=none:gs=on:gsem=off:nwc=1:stl=300:sd=3:ss=priority:sos=on:av=off:sp=reverse_arity:updr=off:uhcvi=on_60"); // MZR 56 (1)
  sched.push("dis-10_2:3_cond=on:fde=none:nwc=1:sd=2:ss=axioms:st=2.0:sos=on:av=off:updr=off:uhcvi=on_60"); // MZR 57 (1)
  sched.push("dis+10_3_cond=fast:fde=unused:gs=on:gsem=off:lwlo=on:nwc=1:sd=3:ss=axioms:sos=on:add=large:afp=10000:afq=2.0:anc=none:sp=reverse_arity_60"); // MZR 58 (1)
  sched.push("lrs+11_4_cond=on:fsr=off:fde=none:gsp=on:gs=on:gsem=on:gsssp=full:nwc=1:stl=300:sd=1:ss=axioms:st=2.0:sac=on:add=off:aer=off:afp=100000:afq=1.4:anc=none:sp=occurrence:updr=off:uhcvi=on_60"); // MZR 59 (1)
  sched.push("ott+10_5:1_bsr=unit_only:er=known:fsr=off:fde=none:gsp=on:lcm=reverse:nwc=2:av=off:sp=reverse_arity:urr=ec_only:uhcvi=on_60"); // MZR 60 (1)
  sched.push("ott+11_3:1_bs=unit_only:bsr=unit_only:br=off:cond=on:fsr=off:fde=none:nwc=1:sd=1:ss=axioms:st=1.5:sos=on:av=off:sp=occurrence:urr=on_60"); // MZR 61 (1)
  sched.push("dis-11_5:1_bd=off:bsr=on:ccuc=small_ones:cond=on:fsr=off:fde=none:gs=on:lcm=predicate:nwc=10:acc=on:aer=off:afp=1000:afq=1.1:sp=occurrence:uhcvi=on_60"); // MZR 62 (1)
  sched.push("dis+11_5_60"); // MZR 63 (1)
  sched.push("lrs+1_8:1_bsr=on:fde=none:gs=on:lcm=reverse:nwc=1:stl=300:sd=2:ss=priority:st=1.5:sos=all:av=off:sp=reverse_arity_60"); // MZR 64 (1)
  sched.push("lrs+11_12_cond=fast:fde=unused:nwc=1:stl=600:sd=2:ss=priority:sos=all:av=off:sp=reverse_arity:uhcvi=on_60"); // MZR 65 (1)
  sched.push("lrs+11_5:1_bsr=unit_only:br=off:cond=fast:fsr=off:gs=on:nwc=1.2:stl=300:sd=1:ss=axioms:st=5.0:sos=all:av=off:sp=reverse_arity:urr=on_60"); // MZR 66 (1)
  sched.push("lrs+1004_5:1_ep=RST:fsr=off:nm=64:nwc=1.2:stl=600:add=off:aer=off:afr=on:afp=100000:afq=1.4:sp=occurrence:updr=off:uhcvi=on_60"); // MZR 67 (1)
  sched.push("dis-11_1_cond=fast:nm=0:nwc=1:sd=2:ss=axioms:sac=on:acc=model:afr=on:afp=100000:afq=1.2:amm=off:anc=all_dependent:sp=reverse_arity:uhcvi=on_60"); // MZR 68 (1)
}

// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------

void Schedules::getLtb2017DefaultSchedule(const Property& property, Schedule& sched) {
  sched.push("lrs-4_5:4_bd=off:bs=unit_only:bsr=on:cond=on:fde=none:gs=on:gsaa=full_model:gsem=off:nm=0:nwc=1.1:nicw=on:stl=300:sd=1:ss=axioms:st=2.0:sos=on:sac=on:afr=on:afp=10000:afq=1.0:amm=off:anc=none:sp=reverse_arity:urr=on:updr=off_60"); // HLL 2 (382)
  sched.push("dis+1002_1_ep=RST:gs=on:gsaa=full_model:gsem=on:nm=64:nwc=1:sd=7:ss=axioms:st=1.2:sos=on:aer=off:afp=40000:afq=1.2:anc=none:updr=off:uhcvi=on_60"); // HLL 3 (170)
  sched.push("dis+1002_1_gs=on:gsem=off:nwc=1:sd=3:ss=axioms:sos=on:sac=on:afp=1000:afq=1.4:amm=sco:anc=none:sp=reverse_arity:urr=on_60"); // HLL 4 (148)
  sched.push("lrs+1011_4:1_bd=off:bsr=unit_only:ccuc=small_ones:fsr=off:fde=unused:gs=on:gsssp=full:nm=64:nwc=4:stl=300:sd=1:ss=priority:sac=on:acc=model:add=large:aer=off:afr=on:afp=100000:afq=1.2:anc=all:uhcvi=on_60"); // HLL 5 (68)
  sched.push("lrs+10_1_bsr=unit_only:cond=fast:gs=on:gsem=off:gsssp=full:lcm=reverse:nwc=1:stl=300:sd=2:ss=axioms:st=5.0:sos=on:sac=on:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:sp=reverse_arity:urr=on:updr=off_60"); // HLL 7 (62)
  sched.push("dis+10_3:1_ep=RST:gsp=on:gs=on:gsem=on:lcm=reverse:nwc=1.1:sd=2:ss=priority:st=2.0:sos=on:sac=on:add=large:aer=off:afp=10000:afq=1.1:anc=none:sp=reverse_arity_60"); // HLL 8 (42)
  sched.push("lrs+1011_3:1_bd=off:bsr=on:cond=fast:gs=on:gsem=on:lwlo=on:nwc=10:stl=300:sd=1:ss=axioms:st=3.0:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // HLL 9 (35)
  sched.push("lrs+1011_5:1_fde=none:gs=on:gsem=on:nwc=4:stl=300:sd=1:ss=axioms:st=5.0:av=off:sp=occurrence:urr=on:uhcvi=on_60"); // HLL 10 (25)
  sched.push("ott+11_2:3_cond=on:ep=RST:fsr=off:fde=none:gsp=on:lcm=predicate:nwc=1:sd=3:ss=priority:sos=all:sac=on:aac=none:aer=off:afp=100000:afq=1.2:anc=all_dependent:urr=ec_only_60"); // HLL 12 (21)
  sched.push("dis+1011_5:1_ep=RSTC:fde=unused:gs=on:gsssp=full:lwlo=on:nm=0:nwc=1:sd=1:ss=axioms:st=3.0:sos=on:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // HLL 13 (16)
  sched.push("dis+1011_5:1_cond=fast:fsr=off:fde=none:gs=on:gsaa=from_current:nwc=3:sd=2:ss=axioms:sac=on:afp=100000:afq=1.0:amm=sco:anc=none:sp=reverse_arity:urr=on:updr=off_60"); // HLL 14 (14)
  sched.push("lrs+11_3_cond=fast:gsp=on:gs=on:gsem=on:gsssp=full:lcm=predicate:nwc=1:stl=300:sd=2:ss=axioms:sos=on:sac=on:add=large:afr=on:afp=100000:afq=1.0:amm=sco:anc=none:updr=off:uhcvi=on_60"); // HLL 15 (14)
  sched.push("dis+1011_2:1_cond=fast:ep=RST:fsr=off:gs=on:gsem=off:gsssp=full:nwc=1:sd=1:ss=axioms:sos=on:add=large:aer=off:afr=on:afp=4000:afq=1.1:anc=none:sp=reverse_arity_60"); // HLL 16 (13)
  sched.push("dis+1011_1_cond=fast:ep=RST:gs=on:nwc=1:sd=2:ss=axioms:st=1.5:sos=on:sac=on:amm=sco:anc=none:urr=ec_only_60"); // HLL 17 (12)
  sched.push("lrs+10_4_bd=off:bsr=unit_only:fde=none:gs=on:lcm=reverse:nwc=1:stl=300:sd=3:ss=axioms:st=3.0:sos=on:av=off:uhcvi=on_60"); // HLL 18 (11)
  sched.push("dis+1002_7_bsr=unit_only:cond=fast:nm=64:nwc=1:sd=1:ss=axioms:sos=on:sac=on:afr=on:afp=100000:afq=1.4:anc=none:uhcvi=on_60"); // HLL 19 (11)
  sched.push("lrs+10_5_bd=off:cond=fast:fde=unused:gsp=on:gs=on:gsem=on:gsssp=full:nwc=1:stl=300:sd=2:ss=axioms:sos=on:av=off:urr=on:updr=off:uhcvi=on_60"); // HLL 20 (10)
  sched.push("dis+1002_3_gs=on:gsem=off:nwc=1.2:sd=2:ss=axioms:st=3.0:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // ISA 1 (1149)
  sched.push("lrs+10_3_ep=RS:gs=on:gsem=off:nm=1024:nwc=1:stl=300:sd=2:ss=priority:sos=all:av=off_60"); // HH4 1 (4899)
  sched.push("ott-11_8:1_bsr=unit_only:lcm=predicate:nwc=1:sd=2:ss=axioms:st=1.2:sos=all:av=off:sp=reverse_arity_60"); // MZR 1 (828)
  sched.push("dis+2_4_bd=off:cond=fast:fsr=off:fde=none:gs=on:gsem=on:lcm=reverse:lwlo=on:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:av=off:sp=occurrence:uhcvi=on_60"); // HLL 21 (9)
  sched.push("dis+1011_3:2_bsr=unit_only:cond=fast:nwc=3:nicw=on:sd=3:ss=priority:add=off:afr=on:afp=10000:afq=1.2:uhcvi=on_60"); // ISA 2 (347)
  sched.push("dis+11_4_cond=on:gsp=on:gs=on:nm=0:nwc=1:sd=2:ss=axioms:st=1.5:sos=on:av=off:urr=on:updr=off:uhcvi=on_60"); // HH4 2 (1018)
  sched.push("ott+1010_3:1_bs=unit_only:bsr=unit_only:br=off:ccuc=first:cond=fast:fde=unused:gs=on:gsem=on:nwc=1:sd=2:ss=axioms:sos=on:sac=on:aac=none:acc=on:aer=off:afp=1000:afq=2.0:anc=all_dependent:sp=reverse_arity:urr=on:updr=off_60"); // MZR 2 (112)
  sched.push("lrs+1010_5:1_bs=unit_only:bsr=on:fde=none:gs=on:gsem=off:gsssp=full:lcm=reverse:nm=0:nwc=4:stl=300:sd=3:ss=priority:st=1.2:sos=on:aac=none:acc=model:afr=on:afp=1000:afq=1.0:amm=off:urr=on:uhcvi=on_60"); // HLL 22 (8)
  sched.push("lrs+1010_1_cond=on:fde=none:gs=on:gsem=off:nwc=1:stl=300:sd=1:ss=axioms:st=3.0:sos=on:sac=on:afp=10000:afq=1.1:amm=sco:anc=none:urr=on:updr=off_60"); // ISA 3 (174)
  sched.push("lrs+11_2:3_br=off:cond=on:fde=none:gs=on:gsem=on:lwlo=on:nm=64:nwc=1:stl=300:sd=1:ss=axioms:st=2.0:sos=all:av=off:sp=occurrence:urr=on:updr=off_60"); // HH4 3 (356)
  sched.push("lrs-11_8:1_bsr=on:cond=on:fde=none:lcm=reverse:nm=0:nwc=1.5:stl=300:sd=2:ss=priority:av=off:sp=occurrence_60"); // HLL 23 (7)
  sched.push("lrs-2_3_ep=RS:gs=on:gsaa=from_current:nwc=1:stl=300:sd=2:ss=axioms:sos=on:sac=on:afr=on:afp=40000:afq=1.0:amm=off:anc=none:sp=reverse_arity:uhcvi=on_60"); // ISA 4 (93)
  sched.push("dis+1002_4_cond=fast:ep=RST:fde=unused:gs=on:gsaa=from_current:gsem=off:nm=0:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:sac=on:add=large:afp=100000:afq=1.0:amm=sco:anc=none:updr=off:uhcvi=on_60"); // HH4 4 (230)
  sched.push("lrs+1004_2_bd=off:ccuc=small_ones:gs=on:gsem=off:gsssp=full:lwlo=on:nm=0:nwc=1:stl=300:sd=4:ss=priority:st=5.0:sos=all:sac=on:acc=on:add=off:aer=off:afp=100000:afq=1.2:anc=none:sp=occurrence:updr=off:uhcvi=on_60"); // MZR 4 (47)
  sched.push("dis+1002_3_cond=on:ep=RS:fsr=off:gs=on:gsaa=full_model:gsem=off:nm=0:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:afp=4000:afq=1.4:amm=off:anc=none:updr=off_60"); // HLL 24 (7)
  sched.push("dis+1011_5_fsr=off:fde=unused:nm=64:nwc=3:sd=2:ss=priority:av=off:sp=occurrence:uhcvi=on_60"); // ISA 5 (58)
  sched.push("lrs+1011_1_cond=fast:fsr=off:fde=unused:gsp=on:gs=on:gsem=off:gsssp=full:nm=0:nwc=10:stl=300:sd=1:ss=axioms:st=5.0:av=off:sp=occurrence:urr=on_60"); // HH4 5 (179)
  sched.push("dis+10_5_bsr=unit_only:cond=on:ep=RS:fde=unused:nm=0:nwc=1:sd=1:ss=axioms:sos=all:av=off_60"); // MZR 5 (37)
  sched.push("dis+1003_5_cond=on:fsr=off:fde=none:gs=on:gsem=off:nwc=1:sos=on:add=large:aer=off:afr=on:afp=100000:afq=1.0:anc=all_dependent:sp=reverse_arity:urr=ec_only:uhcvi=on_60"); // HLL 25 (6)
  sched.push("dis+1002_4_cond=on:gs=on:gsem=off:nwc=1:sd=1:ss=axioms:sos=on:sac=on:afr=on:afp=1000:afq=1.2:amm=sco:anc=none:sp=occurrence:uhcvi=on_60"); // ISA 6 (52)
  sched.push("ott+2_2:1_bd=off:bsr=unit_only:cond=on:gs=on:nwc=1:sd=3:ss=priority:st=1.5:sos=on:av=off:sp=occurrence:updr=off_60"); // HH4 6 (138)
  sched.push("lrs+11_5:1_br=off:cond=fast:fde=unused:gsp=on:gs=on:gsem=on:gsssp=full:lcm=predicate:nm=0:nwc=1:nicw=on:stl=300:sd=1:ss=axioms:st=1.2:sac=on:add=large:afr=on:afp=40000:afq=1.4:amm=sco:anc=all:urr=on_60"); // MZR 6 (32)
  sched.push("lrs+10_5:4_bd=off:gs=on:gsssp=full:lcm=reverse:nwc=1:stl=300:sd=1:ss=axioms:sos=on:sac=on:add=off:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:sp=reverse_arity:updr=off:uhcvi=on_60"); // HLL 26 (6)
  sched.push("dis+1002_4_ep=RST:fsr=off:gs=on:gsem=off:lwlo=on:nwc=1:sd=4:ss=axioms:st=1.5:sos=on:aer=off:afr=on:afp=40000:afq=1.2:anc=none_60"); // ISA 7 (39)
  sched.push("lrs+11_5:4_bd=off:bsr=unit_only:br=off:fsr=off:fde=none:gsp=on:gs=on:gsem=on:nm=0:nwc=1:stl=300:sd=1:ss=axioms:sos=on:add=off:afp=40000:afq=1.4:amm=sco:urr=on:updr=off:uhcvi=on_60"); // HH4 7 (120)
  sched.push("lrs+1011_8:1_cond=on:fde=none:gsp=on:lwlo=on:nwc=1:stl=300:sd=2:ss=axioms:sos=all:av=off:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_60"); // MZR 7 (22)
  sched.push("lrs+11_4:1_br=off:cond=on:fsr=off:fde=unused:gsp=on:gs=on:gsssp=full:lcm=predicate:nm=0:nwc=1:stl=300:sd=1:ss=axioms:av=off:sp=occurrence:urr=on_60"); // HLL 27 (6)
  sched.push("lrs+1011_3:2_bd=off:cond=on:gsp=on:gs=on:gsem=on:nm=0:nwc=4:stl=300:sd=1:ss=axioms:aer=off:afr=on:afp=40000:afq=1.1:anc=all_dependent:sp=reverse_arity:updr=off_60"); // ISA 8 (34)
  sched.push("ott+1011_1_bd=preordered:cond=on:gsp=on:nm=64:nwc=1:sd=3:ss=priority:av=off:sp=reverse_arity:urr=on_60"); // HH4 8 (90)
  sched.push("lrs+11_3_br=off:cond=fast:gs=on:gsem=off:nwc=1:stl=300:sd=3:ss=priority:st=1.5:sos=all:sac=on:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:sp=occurrence:urr=on:uhcvi=on_60"); // MZR 8 (21)
  sched.push("lrs+1010_5_cond=fast:ep=RST:gs=on:gsaa=from_current:gsem=on:nwc=1:stl=300:sd=4:ss=axioms:st=1.5:sos=on:sac=on:add=off:afp=4000:afq=2.0:amm=sco:anc=none:sp=reverse_arity:uhcvi=on_60"); // HLL 28 (6)
  sched.push("dis+1011_1_bsr=on:ccuc=first:nm=0:nwc=4:sd=2:ss=priority:acc=model:add=large:afr=on:amm=off:anc=none:updr=off:uhcvi=on_60"); // ISA 9 (32)
  sched.push("dis+10_2:1_cond=fast:ep=RST:fsr=off:fde=unused:gsp=on:gs=on:gsaa=full_model:gsem=off:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=on:sac=on:add=off:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:urr=on:updr=off:uhcvi=on_60"); // MZR 9 (19)
  sched.push("lrs+11_3_bd=off:cond=fast:fde=none:gsp=on:gs=on:gsaa=from_current:gsem=on:gsssp=full:nwc=1:stl=300:sd=1:ss=axioms:sos=all:add=large:aer=off:afr=on:afp=4000:afq=2.0:anc=none:sp=occurrence:urr=on:updr=off_60"); // HLL 29 (5)
  sched.push("lrs+1002_4_bd=off:fde=none:gs=on:gsaa=from_current:gsem=off:gsssp=full:nwc=1:stl=300:sd=3:ss=axioms:st=5.0:sos=on:aer=off:afp=100000:afq=1.1:anc=none:sp=reverse_arity_60"); // ISA 10 (29)
  sched.push("lrs+11_5_cond=on:ep=RST:fde=none:gsp=on:gs=on:gsem=off:nm=0:nwc=1:stl=300:sd=2:ss=axioms:st=3.0:sos=all:sac=on:add=large:afp=40000:afq=1.4:amm=off:anc=none:urr=ec_only:uhcvi=on_60"); // HH4 10 (70)
  sched.push("lrs+1002_1_bsr=unit_only:nwc=1:stl=300:sd=1:ss=axioms:st=1.5:sos=all:av=off:updr=off:uhcvi=on_60"); // MZR 10 (14)
  sched.push("lrs+4_5:4_bd=off:bs=on:bsr=unit_only:cond=fast:fde=unused:gs=on:gsem=off:nwc=1:stl=300:sd=2:ss=axioms:st=2.0:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // HLL 30 (5)
  sched.push("dis+1002_5_cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=off:gsssp=full:nwc=1:sd=1:ss=axioms:st=5.0:sos=on:sac=on:add=large:afp=40000:afq=1.1:amm=off:anc=none:sp=reverse_arity:updr=off_60"); // ISA 11 (25)
  sched.push("lrs+1011_3_bd=off:bsr=on:cond=fast:fde=none:gs=on:gsssp=full:nm=0:nwc=1:stl=300:sd=2:ss=axioms:sos=all:av=off:sp=occurrence_60"); // HH4 11 (58)
  sched.push("lrs+1_1_bs=on:bsr=on:br=off:cond=fast:fsr=off:gs=on:gsem=off:lwlo=on:nwc=3:stl=300:sd=3:ss=priority:add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:sp=occurrence:urr=on:updr=off_60"); // MZR 11 (11)
  sched.push("lrs+11_5:1_bd=off:br=off:cond=fast:gsp=on:gs=on:gsem=on:gsssp=full:lcm=predicate:nwc=1.1:stl=300:sd=2:ss=priority:st=3.0:av=off:sp=occurrence:urr=on:uhcvi=on_60"); // HLL 31 (5)
  sched.push("dis+1011_3_fde=unused:nm=64:nwc=1:sd=2:ss=axioms:st=5.0:add=off:aer=off:afp=10000:afq=1.0:sp=occurrence_60"); // ISA 12 (20)
  sched.push("lrs-4_5:4_cond=on:gs=on:gsem=on:gsssp=full:nm=64:nwc=1:stl=300:sd=2:ss=axioms:st=2.0:sos=on:sac=on:afp=100000:afq=1.1:amm=sco:anc=none:urr=on_60"); // HH4 12 (44)
  sched.push("lrs-2_1_cond=on:fde=unused:gs=on:gsaa=from_current:gsssp=full:lcm=predicate:nwc=1:stl=300:sd=4:ss=axioms:st=3.0:sos=on:sac=on:afr=on:afp=10000:afq=1.1:anc=none:updr=off_60"); // MZR 12 (11)
  sched.push("dis+1011_3:2_cond=fast:ep=RST:fsr=off:fde=unused:gsp=on:gs=on:gsem=off:nm=0:nwc=1:sd=1:ss=priority:sos=all:add=large:anc=all:sp=occurrence_60"); // HLL 32 (5)
  sched.push("dis+1011_3:1_cond=fast:ep=RS:nm=0:nwc=1.7:sd=2:ss=priority:st=1.2:add=off:afp=10000:afq=1.2:amm=sco:anc=all:sp=occurrence:updr=off:uhcvi=on_60"); // ISA 13 (16)
  sched.push("dis+1011_3:1_br=off:nm=0:nwc=5:sd=1:ss=axioms:sac=on:afp=40000:afq=1.4:amm=sco:anc=none:urr=on:uhcvi=on_60"); // HH4 13 (38)
  sched.push("lrs+10_8:1_bsr=unit_only:br=off:cond=on:fsr=off:gsp=on:gs=on:gsaa=from_current:nm=0:nwc=1:stl=300:sd=2:ss=axioms:st=1.2:sos=on:sac=on:add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:sp=reverse_arity:urr=on:updr=off:uhcvi=on_60"); // MZR 13 (10)
  sched.push("lrs+11_3:1_br=off:cond=fast:ep=R:fsr=off:gs=on:nwc=1:stl=300:sd=2:ss=priority:st=2.0:sos=all:av=off:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // HLL 33 (4)
  sched.push("dis+1002_5_cond=on:ep=RST:fsr=off:fde=unused:gs=on:gsem=on:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:sac=on:add=off:afr=on:amm=sco:anc=none:updr=off:uhcvi=on_60"); // ISA 14 (16)
  sched.push("lrs+11_3:1_bd=off:bsr=unit_only:fsr=off:gs=on:gsaa=from_current:gsem=off:nm=64:nwc=1:stl=300:sd=2:ss=priority:sac=on:amm=sco:anc=none:sp=reverse_arity:updr=off:uhcvi=on_60"); // HH4 14 (36)
  sched.push("dis+11_12_cond=fast:nwc=1:sd=1:ss=axioms:st=1.5:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // MZR 14 (8)
  sched.push("lrs+11_3_bsr=unit_only:cond=on:ep=RST:gsp=on:nwc=1.7:stl=300:sd=3:ss=axioms:st=5.0:sos=all:sac=on:afr=on:afp=100000:afq=1.1:anc=all_dependent:sp=reverse_arity:updr=off:uhcvi=on_60"); // HLL 34 (4)
  sched.push("dis+1011_5_cond=on:er=filter:fde=none:nm=64:nwc=3:sd=2:ss=priority:st=2.0:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // ISA 15 (12)
  sched.push("dis+4_3_bd=off:cond=on:fde=unused:gs=on:gsaa=full_model:gsem=off:gsssp=full:nwc=1:sd=3:ss=axioms:st=3.0:sos=on:add=off:afr=on:afp=10000:afq=1.0:amm=off:anc=none:urr=ec_only:updr=off:uhcvi=on_60"); // HH4 15 (32)
  sched.push("dis+1010_3_bsr=unit_only:cond=fast:fde=none:nwc=1:sd=2:ss=axioms:st=1.5:sos=all:av=off:sp=occurrence:uhcvi=on_60"); // MZR 15 (8)
  sched.push("lrs+10_3:1_cond=on:fde=none:gs=on:gsem=off:gsssp=full:nwc=1.2:stl=300:sd=1:ss=priority:sos=on:sac=on:add=off:afp=1000:afq=1.4:amm=sco:anc=all:sp=reverse_arity:urr=on:updr=off:uhcvi=on_60"); // ISA 16 (12)
  sched.push("dis+1010_5_cond=fast:nm=0:nwc=1:sd=1:ss=axioms:st=1.5:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // HH4 16 (32)
  sched.push("dis+1002_2:3_fde=none:gsp=on:nm=0:nwc=1:sd=3:ss=axioms:sos=on:sac=on:afp=100000:afq=1.0:amm=sco:anc=none:sp=occurrence:updr=off_60"); // MZR 16 (7)
  sched.push("dis+1010_2:3_bs=unit_only:bsr=unit_only:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:gsssp=full:nm=0:nwc=3:sd=4:ss=priority:st=1.5:sos=on:acc=on:add=off:aer=off:afr=on:afp=100000:afq=1.0:sp=reverse_arity:uhcvi=on_60"); // HLL 36 (3)
  sched.push("lrs+11_5_br=off:cond=on:fde=none:gs=on:nwc=1:stl=300:sd=2:ss=axioms:st=3.0:sos=all:add=off:afr=on:afp=40000:afq=1.4:anc=none:sp=reverse_arity:urr=on_60"); // ISA 17 (10)
  sched.push("lrs+11_4:1_bd=off:bsr=unit_only:br=off:fsr=off:fde=unused:gsp=on:gs=on:nm=0:nwc=1:stl=300:sd=1:ss=axioms:sos=on:av=off:sp=reverse_arity:urr=on_60"); // HH4 17 (29)
  sched.push("lrs+10_3:1_fde=unused:lcm=reverse:nwc=1:stl=300:sd=3:ss=priority:st=2.0:sos=all:av=off:sp=occurrence:uhcvi=on_60"); // MZR 17 (6)
  sched.push("dis+1010_5:4_bd=off:fsr=off:fde=unused:gs=on:nm=64:nwc=1:sd=4:ss=axioms:st=1.2:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // HLL 37 (3)
  sched.push("dis+1002_3_bd=off:fde=unused:gs=on:gsaa=from_current:gsem=off:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:afr=on:amm=sco:anc=none:sp=occurrence_60"); // ISA 18 (10)
  sched.push("dis+1002_4_cond=on:gs=on:gsem=off:nwc=1:sd=2:ss=axioms:sos=on:av=off:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_60"); // HH4 18 (28)
  sched.push("lrs+10_2:3_bsr=unit_only:cond=on:fde=none:gs=on:nwc=1:stl=300:sd=2:ss=axioms:sos=on:av=off:sp=reverse_arity_60"); // MZR 18 (6)
  sched.push("lrs+1011_8:1_bd=off:bsr=unit_only:fde=none:gs=on:lwlo=on:nm=0:nwc=1.5:stl=300:sd=1:ss=axioms:st=1.2:av=off:sp=occurrence:updr=off_60"); // HLL 38 (3)
  sched.push("lrs+11_2:3_cond=on:fde=unused:gs=on:gsaa=full_model:nwc=4:stl=300:sd=2:ss=priority:st=5.0:sac=on:add=off:afr=on:amm=off:anc=none:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // HH4 19 (24)
  sched.push("dis+1004_3:1_bsr=unit_only:ep=R:fde=unused:gs=on:gsssp=full:nm=0:nwc=1:sos=all:sac=on:afr=on:afp=10000:afq=2.0:anc=all:sp=reverse_arity:urr=on:updr=off_60"); // MZR 19 (5)
  sched.push("dis+4_5:4_bd=off:fsr=off:fde=unused:gs=on:nwc=1:sd=5:ss=axioms:st=1.5:sos=all:av=off:sp=occurrence:uhcvi=on_60"); // HLL 39 (3)
  sched.push("lrs+1011_4:1_fsr=off:fde=unused:gs=on:gsem=on:gsssp=full:nm=64:nwc=4:stl=300:sd=1:ss=priority:st=3.0:aac=none:acc=on:afr=on:afp=40000:afq=1.2:amm=sco:anc=all:sp=reverse_arity:updr=off:uhcvi=on_60"); // ISA 20 (9)
  sched.push("ott-11_8:1_bsr=unit_only:cond=on:gs=on:gsem=off:gsssp=full:nwc=1.1:sd=2:ss=axioms:sos=on:sac=on:acc=model:add=large:aer=off:afp=40000:afq=2.0:anc=none:sp=reverse_arity:urr=on_60"); // HH4 20 (23)
  sched.push("ott+4_5:1_br=off:cond=fast:fsr=off:nwc=1.3:av=off:sp=occurrence:urr=on:uhcvi=on_60"); // MZR 20 (5)
  sched.push("dis+1011_3_cond=fast:ep=R:gs=on:gsem=off:lwlo=on:nm=0:nwc=1:sd=5:ss=axioms:st=1.5:sos=on:sac=on:add=large:afr=on:afp=1000:afq=1.1:anc=none:uhcvi=on_60"); // HLL 40 (2)
  sched.push("dis+1002_50_fde=unused:nwc=1:sd=2:ss=axioms:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // ISA 21 (8)
  sched.push("lrs+1010_2:1_gs=on:lwlo=on:nm=0:nwc=3:stl=300:sd=4:ss=axioms:av=off_60"); // HH4 21 (22)
  sched.push("dis+1010_1_cond=fast:fsr=off:nwc=1.3:sd=2:ss=axioms:st=1.5:sos=on:acc=model:add=off:afp=4000:afq=2.0:uhcvi=on_60"); // MZR 21 (5)
  sched.push("lrs+1004_3:1_bd=off:bsr=unit_only:cond=fast:fde=none:gs=on:gsem=off:gsssp=full:nwc=1:stl=300:sd=2:ss=axioms:sos=on:av=off:updr=off_60"); // HLL 41 (2)
  sched.push("ott+11_4_cond=fast:fde=none:gs=on:gsem=on:gsssp=full:nwc=1:sd=2:ss=axioms:sos=on:av=off:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // ISA 22 (8)
  sched.push("lrs+1010_4_bsr=unit_only:cond=fast:fsr=off:gs=on:gsaa=from_current:gsem=on:gsssp=full:nm=0:nwc=1:stl=300:sd=1:ss=axioms:st=1.5:sos=on:add=off:aer=off:afr=on:afp=10000:afq=1.0:anc=none:sp=occurrence:urr=on_60"); // HH4 22 (20)
  sched.push("lrs+11_2_bd=off:bsr=unit_only:cond=on:lcm=predicate:lwlo=on:nm=64:nwc=1.1:stl=300:sd=1:ss=axioms:st=2.0:sos=all:av=off_60"); // MZR 22 (5)
  sched.push("lrs+10_1_bd=off:bsr=unit_only:cond=fast:fsr=off:fde=unused:gs=on:gsem=off:lcm=reverse:nwc=1:stl=300:sd=3:ss=axioms:st=1.5:av=off:sp=reverse_arity:urr=on_60"); // HLL 42 (2)
  sched.push("dis-3_3_ep=RST:fde=none:nm=64:nwc=1:sd=4:ss=axioms:sos=on:av=off:sp=occurrence:uhcvi=on_60"); // ISA 23 (7)
  sched.push("dis+2_1_fsr=off:nwc=1:sd=2:ss=axioms:sos=on:av=off:sp=reverse_arity:updr=off:uhcvi=on_60"); // HH4 23 (17)
  sched.push("lrs+10_4:1_bd=off:cond=fast:fde=unused:lcm=reverse:nm=0:nwc=1.2:stl=300:sd=2:ss=axioms:sos=all:av=off_60"); // MZR 23 (5)
  sched.push("lrs+10_4_bd=off:bsr=unit_only:cond=on:gs=on:nwc=1:stl=300:sd=4:ss=axioms:st=5.0:sos=all:av=off:sp=reverse_arity:updr=off:uhcvi=on_60"); // HLL 43 (2)
  sched.push("dis+1010_7_fsr=off:fde=unused:nm=0:nwc=1.3:nicw=on:sd=3:ss=priority:afr=on:afp=100000:afq=1.0:amm=sco:anc=none:updr=off:uhcvi=on_60"); // ISA 24 (7)
  sched.push("ott+2_2:1_cond=fast:fsr=off:fde=unused:gs=on:gsem=off:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // HH4 24 (17)
  sched.push("dis+10_5_ep=RST:fsr=off:gs=on:gsssp=full:lwlo=on:nm=0:nwc=1:sd=4:ss=axioms:sos=on:afr=on:afp=40000:afq=1.1:amm=off:anc=none:uhcvi=on_60"); // MZR 24 (4)
  sched.push("dis+1002_4_cond=fast:ep=RST:fsr=off:nwc=1:sd=3:ss=axioms:st=2.0:sos=on:afp=10000:afq=1.1:amm=sco:sp=occurrence:uhcvi=on_60"); // ISA 25 (6)
  sched.push("lrs+1003_8:1_br=off:cond=on:fde=none:gs=on:gsem=off:nm=0:nwc=1:stl=300:sd=1:ss=axioms:sos=on:add=off:afr=on:afp=40000:afq=1.1:amm=off:anc=none:sp=occurrence:urr=on_60"); // HH4 25 (14)
  sched.push("dis+1002_3_ep=RST:fde=unused:gs=on:gsaa=full_model:gsem=off:nwc=1:sd=1:ss=axioms:st=2.0:sos=on:afp=100000:afq=1.1:anc=none:sp=occurrence:uhcvi=on_60"); // MZR 25 (4)
  sched.push("lrs+1010_2:3_bsr=unit_only:ccuc=small_ones:cond=on:fde=unused:gs=on:gsaa=full_model:nwc=1:stl=300:sd=2:ss=axioms:st=1.5:sos=on:sac=on:acc=model:add=off:aer=off:afr=on:afp=1000:afq=2.0:sp=occurrence:uhcvi=on_60"); // HLL 45 (2)
  sched.push("ott+1011_2_bd=off:ccuc=first:cond=on:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=on:nm=64:nwc=1.3:sd=3:ss=priority:st=1.2:sac=on:acc=on:add=off:afp=4000:afq=1.4:amm=sco:anc=none:urr=ec_only:updr=off:uhcvi=on_60"); // ISA 26 (6)
  sched.push("dis+11_2:1_bd=off:cond=fast:fde=unused:gs=on:gsem=on:nwc=1:sd=3:ss=axioms:st=2.0:sos=all:av=off:sp=occurrence_60"); // HH4 26 (14)
  sched.push("dis+10_5_cond=on:fsr=off:fde=none:gs=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=on:av=off_60"); // MZR 26 (4)
  sched.push("dis+10_1_bd=preordered:bs=unit_only:cond=on:fde=none:lcm=predicate:nwc=1:sd=2:ss=axioms:sos=all:sac=on:afr=on:amm=sco:anc=none:updr=off:uhcvi=on_60"); // HLL 46 (2)
  sched.push("dis+1002_3_bd=off:gs=on:gsem=on:nwc=1.1:sd=7:ss=axioms:st=1.2:sos=on:av=off:sp=reverse_arity:updr=off_60"); // ISA 27 (5)
  sched.push("lrs+1011_3:1_bd=off:cond=fast:fsr=off:fde=unused:gs=on:nm=0:nwc=5:stl=300:sd=2:ss=axioms:afp=100000:afq=1.4:amm=off:anc=none:sp=occurrence:urr=on_60"); // HH4 27 (14)
  sched.push("ott-11_8:1_bd=preordered:ccuc=first:er=known:fsr=off:fde=unused:gsp=on:lcm=predicate:nm=0:nwc=2:sd=3:ss=axioms:acc=on:afp=10000:afq=2.0:amm=sco:sp=occurrence:updr=off_60"); // MZR 27 (4)
  sched.push("lrs+11_5_bd=off:bsr=unit_only:cond=on:fsr=off:gs=on:gsaa=from_current:gsssp=full:nwc=1:stl=300:sd=1:ss=axioms:st=5.0:sos=all:add=off:afp=4000:afq=2.0:amm=off:anc=none:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // HLL 47 (2)
  sched.push("dis+11_2:3_cond=on:gs=on:gsem=off:gsssp=full:lcm=reverse:nwc=1:sd=1:ss=axioms:st=1.5:add=off:aer=off:afr=on:afp=1000:afq=2.0:anc=all_dependent:sp=reverse_arity:updr=off:uhcvi=on_60"); // ISA 28 (5)
  sched.push("dis+1011_3_cond=on:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:sac=on:afr=on:afp=1000:afq=1.4:anc=none:sp=occurrence:updr=off:uhcvi=on_60"); // HH4 28 (13)
  sched.push("dis+11_2:1_br=off:ep=RST:fde=unused:gsp=on:gs=on:gsaa=from_current:gsem=off:nwc=1:sd=1:ss=priority:st=1.2:sos=all:add=large:aer=off:afp=100000:afq=1.1:anc=none:sp=occurrence:urr=on_60"); // HLL 48 (2)
  sched.push("dis+11_2:1_fde=none:gsp=on:nwc=1:sd=2:ss=axioms:sos=all:av=off:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // HH4 29 (13)
  sched.push("lrs+1011_1_cond=on:fsr=off:gs=on:nwc=1:stl=300:sd=4:ss=priority:st=1.2:sos=on:av=off:sp=reverse_arity:urr=on_60"); // MZR 29 (3)
  sched.push("dis+1011_2:3_cond=fast:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:gsssp=full:nm=0:nwc=1:sd=2:ss=axioms:sos=on:sac=on:add=large:afr=on:afp=1000:afq=2.0:anc=none:sp=reverse_arity:urr=ec_only:uhcvi=on_60"); // HLL 49 (2)
  sched.push("dis+1002_3_cond=fast:ep=RSTC:fsr=off:gs=on:gsem=off:lwlo=on:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:av=off:sp=occurrence:uhcvi=on_60"); // ISA 30 (4)
  sched.push("lrs+11_3_bsr=unit_only:cond=fast:fsr=off:fde=none:gsp=on:nwc=5:stl=300:sd=3:ss=priority:st=2.0:av=off:updr=off:uhcvi=on_60"); // HH4 30 (12)
  sched.push("lrs+11_3:1_bsr=unit_only:br=off:cond=on:ep=RST:fsr=off:gs=on:gsaa=from_current:gsem=off:nwc=3:stl=300:sd=2:ss=axioms:st=2.0:sac=on:add=large:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:sp=reverse_arity:urr=on_60"); // MZR 30 (3)
  sched.push("lrs+1003_4_bsr=unit_only:cond=fast:fsr=off:gsp=on:gs=on:gsaa=from_current:nm=0:nwc=1:stl=300:sos=on:sac=on:add=large:afp=10000:afq=1.1:anc=none:urr=ec_only:uhcvi=on_60"); // HLL 50 (1)
}

void Schedules::getHigherOrderSchedule2020(Schedule& quick, Schedule& fallback)
{
  //no fallback at present
  quick.push("ott+1002_2_av=off:bd=preordered:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:irw=on:lma=on:nm=64:nwc=10:sp=reverse_arity:updr=off_2");
  quick.push("lrs-11_4:1_afp=4000:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_2");
  quick.push("lrs+1011_8_add=large:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3");
  quick.push("dis+10_128_acc=on:add=off:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afp=4000:afq=1.4:amm=off:bd=preordered:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_2");
  quick.push("lrs+1010_8_add=off:afp=100000:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afq=1.0:amm=off:anc=none:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:stl=30:sp=reverse_arity:urr=on_13");
  quick.push("ott+1002_8:1_add=off:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sp=occurrence:urr=on:updr=off_14");
  quick.push("lrs+1011_5:1_acc=on:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3");
  quick.push("lrs+4_3_av=off:br=off:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32");
  quick.push("dis+1010_3:2_av=off:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:gsp=on:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29");
  quick.push("dis+1_2:3_acc=on:add=large:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=on:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3");
  quick.push("dis+10_128_acc=on:add=off:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_40");
  quick.push("dis-11_3_add=off:afp=40000:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_2");
  quick.push("dis+1002_6_add=large:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_2");
  quick.push("lrs+1010_3_av=off:fsr=off:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9");
  quick.push("lrs+1002_1_av=off:er=filter:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1:stl=30:sd=3:ss=axioms:st=1.5:sos=on_1");
  quick.push("ott+2_2_afp=10000:afq=1.4:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:amm=off:anc=none:gsp=on:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_7");
  quick.push("lrs+1010_3:2_afr=on:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afp=100000:afq=1.1:anc=none:gsp=on:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:sac=on:sp=occurrence_300");
  quick.push("lrs+1011_5:1_acc=on:csup=on:inj=on:e2e=on:prag=on:cases=on:cnfonf=eager:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_30");
  quick.push("ott+11_20_afr=on:afp=100000:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_6");
  quick.push("dis+1002_3:1_acc=model:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=on:irw=on:nm=16:nwc=1:sos=all_8");
  quick.push("lrs+10_12_add=off:afp=100000:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41");
  quick.push("lrs-11_4:1_afp=4000:csup=on:inj=on:chr=on:cases=on:cnfonf=lazy_gen:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_30");
  quick.push("dis+10_4_av=off:bsr=on:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:cond=fast:er=filter:fde=none:gsp=on:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8");
  quick.push("lrs+1002_1_add=large:csup=on:inj=on:fe=off:chr=on:cases=on:cnfonf=eager:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_50");
  quick.push("lrs+1011_5_add=large:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_130");
  quick.push("lrs+1010_8_add=off:afp=100000:csup=on:inj=off:cases=on:chr=off:e2e=on:cnfonf=eager:afq=1.0:amm=off:anc=none:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:stl=30:sp=reverse_arity:urr=on_13");
  quick.push("lrs+1_4_afp=100000:afq=1.2:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:anc=none:bd=off:cond=on:gs=on:gsem=off:nm=64:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:updr=off_300");
  quick.push("lrs-11_4:1_afp=4000:csup=on:inj=on:mXXn=1:cases=on:e2e=on:cnfonf=eager:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_186");
  quick.push("dis+1002_4_add=large:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afp=40000:afq=1.0:anc=none:cond=fast:fde=none:gs=on:gsaa=full_model:lma=on:lwlo=on:nm=0:nwc=1.5:sp=reverse_arity:tha=off_300");
  quick.push("dis-11_3_add=off:afp=40000:csup=on:inj=on:chr=on:e2e=on:prag=on:cases=on:cnfonf=eager:afq=1.0:fde=all:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_50");
  quick.push("dis+1011_10_add=large:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_75");
  quick.push("dis+1010_3:2_av=off:csup=on:prag=on:chr=on:cases=on:bet=on:cnfonf=lazy_not_be_gen:gsp=on:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29");
  quick.push("lrs+1011_8_add=large:csup=on:inj=on:prag=on:cases=on:cnfonf=eager:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_26");
  quick.push("lrs+1011_8_add=large:csup=on:fe=off:cases=on:cnfonf=eager:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_30");
  quick.push("dis+1002_4_add=large:csup=on:narr=off:inj=on:prag=on:cbe=off:cases=on:cnfonf=eager:afp=40000:afq=1.0:anc=none:cond=fast:fde=none:gs=on:gsaa=full_model:lma=on:lwlo=on:nm=0:nwc=1.5:sp=reverse_arity_27");
  quick.push("dis+1_3_add=large:afp=4000:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sos=all:sac=on:updr=off:uhcvi=on_125");
  quick.push("dis+1010_3:1_av=off:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_77");
  quick.push("lrs+1011_5:4_acc=on:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126");
  quick.push("lrs+1002_1_add=large:csup=on:narr=off:inj=on:fe=off:chr=on:cases=on:cnfonf=eager:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_50");
  quick.push("lrs-3_4:1_afp=1000:afq=1.4:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11");
  quick.push("ott+11_2:1_add=large:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_9");
  quick.push("lrs+1011_8_add=large:csup=off:cases=on:cnfonf=eager:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_13");
  quick.push("lrs+1011_2:1_av=off:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:irw=on:lwlo=on:nm=16:newcnf=on:nwc=2:sd=4:ss=axioms:st=3.0:sp=occurrence_300");
  quick.push("dis+1011_4_av=off:cond=on:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5");
  quick.push("lrs+10_3:1_av=off:bsr=on:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73");
  quick.push("dis+10_1_add=off:afp=4000:csup=on:inj=on:chr=on:e2e=on:cases=on:cnfonf=eager:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_12");
  quick.push("lrs+4_3_av=off:bd=preordered:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:bs=unit_only:cond=fast:fde=unused:gsp=on:gs=on:gsem=on:lma=on:lwlo=on:nm=6:nwc=1:stl=60:sp=occurrence:uhcvi=on_481");
  quick.push("lrs+1002_1_av=off:fde=unused:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:lwlo=on:nm=16:nwc=4:sp=occurrence_300");
  quick.push("ott+1002_2_av=off:bd=preordered:csup=on:inj=on:chr=on:cases=on:cnfonf=lazy_not_gen_be_off:bet=on:sup=off:irw=on:lma=on:nm=64:nwc=10:sp=reverse_arity:updr=off_70");
  quick.push("lrs-11_4:1_afp=4000:csup=on:inj=on:bet=on:cases=on:cnfonf=lazy_not_gen_be_off:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_45");
  quick.push("lrs+1011_8_add=large:csup=on:e2e=on:prag=on:mXXn=1:cnfonf=lazy_simp:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_19");
  quick.push("dis+1011_4_av=off:cond=on:piset=false_true_not:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5");
  quick.push("dis+1002_7_acc=on:afp=4000:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=on:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73");
  quick.push("dis+11_24_afp=40000:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91");
  quick.push("lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:csup=on:cases=on:ptlr=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:stl=30:sp=reverse_arity:urr=on_13");
  quick.push("lrs+1011_5_afr=on:afp=100000:narr=ski:prag=on:mXXn=3:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:stl=30:sac=on:urr=on_15");
  quick.push("lrs+1011_5:4_acc=on:narr=off:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:add=large:afr=on:afp=0:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_12");
  quick.push("lrs+1011_8_add=large:csup=on:narr=off:fe=off:cases=on:cnfonf=eager:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_10");
  quick.push("lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:csup=on:cases=on:ptlr=on:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_10");
  quick.push("lrs+1011_8_add=large:csup=on:piset=all:inj=on:chr=on:cases=on:cnfonf=eager:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_31");
  quick.push("lrs+1_8:1_av=off:cond=fast:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:fde=unused:lcm=predicate:nm=16:nwc=10:sp=occurrence:urr=ec_only_600");
  quick.push("dis+1011_5_add=off:afr=on:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2");
  quick.push("lrs-11_4:1_afp=0:narr=sk:prag=on:csup=on:inj=on:mXXn=1:cases=on:e2e=on:cnfonf=eager:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_186");
  quick.push("dis+1002_6_add=large:csup=on:narr=sk:prag=on:mXXn=4:inj=on:chr=on:cases=on:cnfonf=eager:afp=0:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_22");
  quick.push("lrs-11_4:1_afp=0:fe=axiom:narr=sk:prag=on:csup=on:inj=on:mXXn=1:cases=on:e2e=on:cnfonf=eager:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_186");
  quick.push("dis+1_3_add=large:afp=4000:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sos=all:sac=on:updr=off:uhcvi=on_300");
  quick.push("lrs+1011_10_aac=none:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38");
  quick.push("lrs+10_1:1_av=off:bsr=on:csup=on:fe=axiom:cases=on:cnfonf=eager:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_67");
  quick.push("ott+11_2:1_add=large:narr=ski:prag=on:mXXn=4:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:afp=0:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_9");
  quick.push("ott+1002_8:1_add=off:csup=on:fe=axiom:chr=on:cases=on:cnfonf=eager:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sp=occurrence:urr=on:updr=off_15");
  quick.push("dis+1011_10_add=large:csup=on:narr=off:inj=on:chr=on:cases=on:cnfonf=eager:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_20");
  quick.push("lrs-11_4:1_afp=0:fe=axiom:narr=off:csup=on:inj=on:chr=on:cases=on:cnfonf=lazy_gen:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_30");
  quick.push("lrs+1011_5_add=large:csup=on:fe=axiom:ntd=on:inj=on:chr=on:cases=on:cnfonf=eager:afp=0:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_40");
  quick.push("lrs+1002_1_av=off:csup=on:e2e=on:cs=on:fde=unused:lwlo=on:nm=16:nwc=4:sp=occurrence_150");
  quick.push("ott+2_1:1_csup=on:afp=0:fe=axiom:narr=off:prag=on:cs=on_50");
  quick.push("lrs+1011_2:1_av=off:fe=axiom:narr=off:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:irw=on:lwlo=on:nm=16:newcnf=on:nwc=2:sd=4:ss=axioms:st=3.0:sp=occurrence_100");
  quick.push("lrs+1011_2:1_av=off:piset=small_set:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:irw=on:lwlo=on:nm=16:newcnf=on:nwc=2:sd=4:ss=axioms:st=3.0:sp=occurrence_200");
  quick.push("lrs+1011_2:1_av=off:irw=off:csup=on:e2e=on:cs=on:lwlo=on:nm=16:newcnf=on:nwc=2:sd=4:ss=axioms:st=3.0:sp=occurrence_30");
  quick.push("dis+1011_10_add=large:csup=on:fe=axiom:narr=off:inj=on:chr=on:cases=on:cnfonf=eager:afr=on:afp=4000:afq=1.0:amm=off:anc=none:afp=0:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_20");
  quick.push("dis+1002_4_add=large:afp=40000:afq=1.5:csup=on:e2e=on:cs=on:anc=none:cond=fast:fde=none:gs=on:gsaa=full_model:lma=on:lwlo=on:nm=0:nwc=1.5:sp=reverse_arity:tha=off_44");
  quick.push("lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:csup=on:e2e=on:cs=on:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_43");
  quick.push("lrs+4_3_av=off:bd=preordered:bs=unit_only:cond=fast:csup=on:e2e=on:cs=on:fde=unused:gsp=on:gs=on:gsem=on:lma=on:lwlo=on:nm=6:nwc=1:stl=60:sp=occurrence:uhcvi=on_100");
  quick.push("lrs-3_4:1_afp=1000:afq=1.4:csup=on:e2e=on:cs=on:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11");
  quick.push("ott+2_1:1_csup=on:prag=on:cs=on:inj=on:mXXn=1_170");
  quick.push("dis-11_3_add=off:afp=0:fe=axiom:csup=on:inj=on:chr=on:e2e=on:prag=on:cases=on:cnfonf=eager:afq=1.0:fde=all:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_50");
  quick.push("lrs+1011_5:1_acc=on:fe=axiom:csup=on:inj=on:e2e=on:prag=on:cases=on:cnfonf=eager:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:afp=0:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_30");
  quick.push("ott+1002_2_av=off:bd=preordered:narr=off:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:irw=on:lma=on:nm=64:nwc=10:sp=reverse_arity:updr=off_20");
  quick.push("lrs-11_4:1_afp=4000:narr=off:csup=on:inj=on:chr=on:cases=on:cnfonf=lazy_gen:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_30");
  quick.push("lrs+1011_2:1_av=off:irw=off:ntd=on:csup=on:e2e=on:cs=on:lwlo=on:nm=16:newcnf=on:nwc=2:sd=4:ss=axioms:st=3.0:sp=occurrence_30");
  quick.push("lrs+1010_3:2_afr=on:csup=on:ntd=on:inj=on:chr=on:cases=on:cnfonf=eager:afp=100000:afq=1.1:anc=none:gsp=on:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:sac=on:sp=occurrence_300");
  quick.push("lrs+1_8:1_av=off:fe=axiom:cond=fast:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:fde=unused:lcm=predicate:nm=16:nwc=10:sp=occurrence:urr=ec_only_300");
  quick.push("ott+2_1:1_csup=on:narr=off:prag=on:cs=on_110");
  quick.push("lrs+1011_2:1_av=off:narr=off:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:irw=on:lwlo=on:nm=16:newcnf=on:nwc=2:sd=4:ss=axioms:st=3.0:sp=occurrence_200");
  quick.push("lrs+1011_5_add=large:csup=on:ntd=on:inj=on:chr=on:cases=on:cnfonf=eager:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_130");
  quick.push("lrs+1011_5_add=large:csup=on:fe=axiom:inj=on:chr=on:cases=on:cnfonf=eager:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_130");
  quick.push("lrs+1011_8_add=large:csup=on:fe=axiom:e2e=on:prag=on:mXXn=1:cnfonf=lazy_simp:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_19");
  quick.push("lrs+1011_8_add=large:csup=on:fe=axiom:piset=all:inj=on:chr=on:cases=on:cnfonf=eager:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_31");
  quick.push("ott+1002_2_av=off:bd=preordered:csup=on:inj=on:cvc=on:chr=on:cases=on:cnfonf=eager:irw=on:lma=on:nm=64:nwc=10:sp=reverse_arity:updr=off_2");
  quick.push("lrs-11_4:1_afp=4000:csup=on:inj=on:chr=on:cvc=on:cases=on:cnfonf=eager:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_2");
  quick.push("lrs+1011_8_add=large:csup=on:inj=on:chr=on:cvc=on:cases=on:cnfonf=eager:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3");
  quick.push("dis+10_128_acc=on:add=off:csup=on:inj=on:chr=on:cvc=on:cases=on:cnfonf=eager:afp=4000:afq=1.4:amm=off:bd=preordered:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_2");
  quick.push("lrs+1010_8_add=off:afp=100000:csup=on:inj=on:chr=on:cvc=on:cases=on:cnfonf=eager:afq=1.0:amm=off:anc=none:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:stl=30:sp=reverse_arity:urr=on_13");
  quick.push("ott+1002_8:1_add=off:csup=on:inj=on:chr=on:cases=on:cvc=on:cnfonf=eager:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sp=occurrence:urr=on:updr=off_14");
  quick.push("lrs+1011_5:1_acc=on:csup=on:inj=on:chr=on:cases=on:cvc=on:cnfonf=eager:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3");
  quick.push("lrs+4_3_av=off:br=off:csup=on:inj=on:chr=on:cases=on:cvc=on:cnfonf=eager:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32");
  quick.push("dis+1010_3:2_av=off:csup=on:inj=on:chr=on:cases=on:cvc=on:cnfonf=eager:gsp=on:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29");
  quick.push("dis+1_2:3_acc=on:add=large:csup=on:inj=on:chr=on:cases=on:cvc=on:cnfonf=eager:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=on:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3");
  quick.push("dis+10_128_acc=on:add=off:add=off:afp=4000:afq=1.4:amm=off:cvc=on:bd=preordered:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_40");
  quick.push("dis-11_3_add=off:afp=40000:csup=on:inj=on:chr=on:cases=on:cvc=on:cnfonf=eager:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_2");
  quick.push("dis+1002_6_add=large:csup=on:inj=on:chr=on:cases=on:cvc=on:cnfonf=eager:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_2");
  quick.push("lrs+1010_3_av=off:fsr=off:csup=on:inj=on:chr=on:cases=on:cvc=on:cnfonf=eager:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9");
  quick.push("lrs+1002_1_av=off:er=filter:csup=on:inj=on:chr=on:cases=on:cvc=on:cnfonf=eager:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1:stl=30:sd=3:ss=axioms:st=1.5:sos=on_1");
  quick.push("ott+2_2_afp=10000:afq=1.4:csup=on:inj=on:chr=on:cases=on:cvc=on:cnfonf=eager:amm=off:anc=none:gsp=on:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_7");
  quick.push("lrs+1010_3:2_afr=on:csup=on:inj=on:chr=on:cases=on:cvc=on:cnfonf=eager:afp=100000:afq=1.1:anc=none:gsp=on:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:sac=on:sp=occurrence_300");
  quick.push("lrs+1011_5:1_acc=on:csup=on:inj=on:e2e=on:prag=on:cvc=on:cases=on:cnfonf=eager:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_30");
  quick.push("ott+11_20_afr=on:afp=100000:csup=on:inj=on:chr=on:cvc=on:cases=on:cnfonf=eager:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_6");
  quick.push("dis+1002_3:1_acc=model:csup=on:inj=on:chr=on:cases=on:cvc=on:cnfonf=eager:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=on:irw=on:nm=16:nwc=1:sos=all_8");
  quick.push("lrs+10_12_add=off:afp=100000:csup=on:inj=on:chr=on:cases=on:cvc=on:cnfonf=eager:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41");
  quick.push("lrs-11_4:1_afp=4000:csup=on:inj=on:chr=on:cases=on:cvc=on:cnfonf=lazy_gen:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_30");
  quick.push("dis+10_4_av=off:bsr=on:csup=on:cvc=on:inj=on:chr=on:cases=on:cnfonf=eager:cond=fast:er=filter:fde=none:gsp=on:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8");
  quick.push("lrs+1002_1_add=large:csup=on:inj=on:cvc=on:fe=off:chr=on:cases=on:cnfonf=eager:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_50");
  quick.push("lrs+1011_5_add=large:csup=on:inj=on:cvc=on:chr=on:cases=on:cnfonf=eager:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_130");
  quick.push("lrs+1010_8_add=off:afp=100000:csup=on:cvc=on:inj=off:cases=on:chr=off:e2e=on:cnfonf=eager:afq=1.0:amm=off:anc=none:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:stl=30:sp=reverse_arity:urr=on_13");
  quick.push("lrs+1_4_afp=100000:afq=1.2:csup=on:inj=on:cvc=on:chr=on:cases=on:cnfonf=eager:anc=none:bd=off:cond=on:gs=on:gsem=off:nm=64:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:updr=off_300");
  quick.push("lrs-11_4:1_afp=4000:csup=on:inj=on:mXXn=1:cvc=on:cases=on:e2e=on:cnfonf=eager:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_186");
  quick.push("dis+1002_4_add=large:csup=on:inj=on:chr=on:cvc=on:cases=on:cnfonf=eager:afp=40000:afq=1.0:anc=none:cond=fast:fde=none:gs=on:gsaa=full_model:lma=on:lwlo=on:nm=0:nwc=1.5:sp=reverse_arity:tha=off_300");
  quick.push("dis-11_3_add=off:afp=40000:csup=on:inj=on:cvc=on:chr=on:e2e=on:prag=on:cases=on:cnfonf=eager:afq=1.0:fde=all:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_50");
  quick.push("dis+1011_10_add=large:csup=on:inj=on:chr=on:cvc=on:cases=on:cnfonf=eager:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_75");
  quick.push("dis+1010_3:2_av=off:csup=on:prag=on:chr=on:cvc=on:cases=on:bet=on:cnfonf=lazy_not_be_gen:gsp=on:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29");
  quick.push("lrs+1011_8_add=large:csup=on:inj=on:prag=on:cvc=on:cases=on:cnfonf=eager:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_26");
  quick.push("lrs+1011_8_add=large:csup=on:fe=off:cases=on:cvc=on:cnfonf=eager:afp=100000:afq=1.1:er=filter:gsp=on:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_30");
  quick.push("dis+1002_4_add=large:csup=on:narr=off:inj=on:cvc=on:prag=on:cbe=off:cases=on:cnfonf=eager:afp=40000:afq=1.0:anc=none:cond=fast:fde=none:gs=on:gsaa=full_model:lma=on:lwlo=on:nm=0:nwc=1.5:sp=reverse_arity_27");
  quick.push("dis+1_3_add=large:afp=4000:csup=on:inj=on:cvc=on:chr=on:cases=on:cnfonf=eager:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sos=all:sac=on:updr=off:uhcvi=on_125");
  quick.push("dis+1010_3:1_av=off:csup=on:inj=on:chr=on:cvc=on:cases=on:cnfonf=eager:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_77");
  quick.push("lrs+1010_3_av=off:fsr=off:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_650");
  quick.push("dis-11_3_add=off:afp=0:fe=axiom:mXXn=2:csup=on:inj=on:chr=on:e2e=on:prag=on:cases=on:cnfonf=eager:afq=1.0:fde=all:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_600");
  quick.push("lrs+4_3_av=off:bd=preordered:fe=axiom:narr=off:csup=on:ntd=on:inj=on:chr=on:cases=on:cnfonf=lazy_simp:bs=unit_only:cond=fast:fde=unused:gsp=on:gs=on:gsem=on:lma=on:lwlo=on:nm=6:nwc=1:stl=60:sp=occurrence:uhcvi=on_600");
  quick.push("ott+2_1:1_csup=on:fe=axiom:ntd=on:narr=off:prag=on:cs=on_600");
}

// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------

void Schedules::getInductionSchedule(const Shell::Property& property, Schedule& quick, Schedule& fallback) {
  bool struct_induction = (property.props() & (Property::PR_HAS_DT_CONSTRUCTORS | Property::PR_HAS_CDT_CONSTRUCTORS));
  bool integer_induction = (property.props() & Property::PR_HAS_INTEGERS);
  if (!struct_induction && integer_induction) {
    getIntegerInductionSchedule(property, quick, fallback);
  } else if (struct_induction && !integer_induction) {
    getStructInductionSchedule(property, quick, fallback);
  } else if (struct_induction && integer_induction) {
    quick.push("dis+1002_1_aac=none:anc=all:ind=both:sos=theory:sac=on:sstl=1:to=lpo_30");
    quick.push("lrs+10_1_av=off:br=off:ind=both:urr=on_89");
    quick.push("lrs+10_1_drc=off:iik=one:ind=both_89");
    quick.push("lrs+10_1_drc=off:iik=one:ind=both:indoct=on:sos=theory:sstl=1_89");
    quick.push("lrs+10_1_drc=off:iik=one:ind=both:indoct=on:sos=theory:sstl=1:to=lpo_89");
    quick.push("lrs+10_1_drc=off:iik=one:ind=both:sos=theory:sstl=1_89");
    quick.push("lrs+10_1_drc=off:iik=one:ind=both:sos=theory:sstl=1:to=lpo_89");
    quick.push("lrs+10_1_drc=off:iik=one:ind=both:to=lpo_89");
    quick.push("lrs+10_1_iik=one:ind=both_89");
    quick.push("lrs+10_1_iik=one:ind=both:indoct=on:sos=theory:sstl=1_89");
    quick.push("lrs+10_1_iik=one:ind=both:indoct=on:sos=theory:sstl=1:to=lpo_89");
    quick.push("lrs+10_1_iik=one:ind=both:sos=theory:sstl=1_89");
    quick.push("lrs+10_1_iik=one:ind=both:sos=theory:sstl=1:to=lpo_89");
    quick.push("lrs+10_1_iik=one:ind=both:to=lpo_89");
    // Configurations targeted mainly at integer induction
    quick.push("lrs+10_1_iik=one:ind=both:indoct=on_100");
    quick.push("lrs+11_1_drc=off:iik=one:ind=both:indoct=on:sos=theory:sstl=1:to=lpo:uwa=one_side_interpreted_100");
    quick.push("lrs+10_1_asg=force:canc=force:drc=off:ev=force:gve=force:iik=one:ind=both:indmd=1:intindstcomp=none:pum=on:to=lpo:urr=on_100");
    quick.push("lrs+10_1_iik=one:ind=both:indmd=1:intindstcomp=none_100");
    quick.push("lrs+1010_2_drc=off:iik=one:ind=both:indoct=on:sos=theory:sstl=1:to=lpo:uwa=one_side_interpreted_100");
    quick.push("lrs+10_1_drc=off:iik=one:ind=both:indoct=on:sos=theory:sstl=1:to=lpo_100");
    quick.push("lrs+10_1_iik=one:ind=both:intinddb=on:intindsteq=toplevel_not_in_other:intindstcomp=always:intindstterm=none_100");
    quick.push("lrs+1010_2_asg=force:canc=force:drc=off:ev=force:gve=force:iik=one:ind=both:indoct=on:pum=on:to=lpo:urr=on:uwa=one_side_interpreted_30");
    quick.push("lrs+10_1_drc=off:iik=one:ind=both:indoct=on:intindsteq=not_in_both:intindstcomp=only_one_occurrence:intindstterm=no_skolems:sos=theory:sstl=1:to=lpo_30");
    quick.push("lrs+10_1_asg=force:canc=force:drc=off:ev=force:gve=force:iik=one:ind=both:indgen=on:indmd=1:intindstcomp=not_in_both:intindstterm=none:pum=on:to=lpo:urr=on_30");
    quick.push("lrs+11_1_asg=force:canc=force:drc=off:ev=force:gve=force:iik=one:ind=both:intinddb=on:intindsteq=toplevel_not_in_other:intindstcomp=always:intindstterm=none:pum=on:to=lpo:urr=on:uwa=one_side_interpreted_100");
    quick.push("lrs+10_1_drc=off:iik=one:ind=both:intinddb=on:intindsteq=toplevel_not_in_other:intindstcomp=always:intindstterm=none:sos=theory:sstl=1:to=lpo_100");
    quick.push("lrs+11_1_asg=force:canc=force:drc=off:ev=force:gve=force:iik=one:ind=both:indoct=on:intinddb=on:intindsteq=toplevel_not_in_other:intindstcomp=only_one_occurrence:pum=on:to=lpo:urr=on:uwa=one_side_interpreted_100");
    quick.push("dis+1002_1_aac=none:anc=all:iik=one:ind=both:sos=theory:sac=on:sstl=1:to=lpo_30");
  } else {
    // No induction is on.
    quick.push("lrs+10_1__90");
  }

  fallback.push("lrs+10_1__50");
}

// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------

void Schedules::getIntegerInductionSchedule(const Shell::Property& property, Schedule& quick, Schedule& fallback) {
  quick.push("lrs+10_1_iik=one:ind=int:indoct=on_100");
  quick.push("lrs+11_1_drc=off:iik=one:ind=int:indoct=on:sos=theory:sstl=1:to=lpo:uwa=one_side_interpreted_100");
  quick.push("lrs+10_1_asg=force:canc=force:drc=off:ev=force:gve=force:iik=one:ind=int:indmd=1:intindstcomp=none:pum=on:to=lpo:urr=on_100");
  quick.push("lrs+10_1_iik=one:ind=int:indmd=1:intindstcomp=none_100");
  quick.push("lrs+1010_2_drc=off:iik=one:ind=int:indoct=on:sos=theory:sstl=1:to=lpo:uwa=one_side_interpreted_100");
  quick.push("lrs+10_1_drc=off:iik=one:ind=int:indoct=on:sos=theory:sstl=1:to=lpo_100");
  quick.push("lrs+10_1_iik=one:ind=int:intinddb=on:intindsteq=toplevel_not_in_other:intindstcomp=always:intindstterm=none_100");
  quick.push("lrs+1010_2_asg=force:canc=force:drc=off:ev=force:gve=force:iik=one:ind=int:indoct=on:pum=on:to=lpo:urr=on:uwa=one_side_interpreted_30");
  quick.push("lrs+10_1_drc=off:iik=one:ind=int:indoct=on:intindsteq=not_in_both:intindstcomp=only_one_occurrence:intindstterm=no_skolems:sos=theory:sstl=1:to=lpo_30");
  quick.push("lrs+10_1_asg=force:canc=force:drc=off:ev=force:gve=force:iik=one:ind=int:indgen=on:indmd=1:intindstcomp=not_in_both:intindstterm=none:pum=on:to=lpo:urr=on_30");
  quick.push("lrs+11_1_asg=force:canc=force:drc=off:ev=force:gve=force:iik=one:ind=int:intinddb=on:intindsteq=toplevel_not_in_other:intindstcomp=always:intindstterm=none:pum=on:to=lpo:urr=on:uwa=one_side_interpreted_100");
  quick.push("lrs+10_1_drc=off:iik=one:ind=int:intinddb=on:intindsteq=toplevel_not_in_other:intindstcomp=always:intindstterm=none:sos=theory:sstl=1:to=lpo_100");
  quick.push("lrs+11_1_asg=force:canc=force:drc=off:ev=force:gve=force:iik=one:ind=int:indoct=on:intinddb=on:intindsteq=toplevel_not_in_other:intindstcomp=only_one_occurrence:pum=on:to=lpo:urr=on:uwa=one_side_interpreted_100");
  quick.push("dis+1002_1_aac=none:anc=all:iik=one:ind=int:sos=theory:sac=on:sstl=1:to=lpo_30");
  quick.push("lrs+10_1_av=off:br=off:iik=one:ind=int:urr=on_90");
  quick.push("lrs+10_1_avsq=on:drc=off:iik=one:ind=int:to=lpo_30");
  quick.push("lrs+10_1_drc=off:iik=one:ind=int_30");
  quick.push("lrs+10_1_drc=off:iik=one:ind=int:thsq=on:thsqd=16:to=lpo_30");
  quick.push("lrs+10_1_drc=off:iik=one:ind=int:to=lpo_30");
  quick.push("lrs+10_1_iik=one:ind=int_30");
  quick.push("lrs+4_5_drc=off:iik=one:ind=int:plsq=on:to=lpo_100");

  fallback.push("lrs+10_1_iik=one:ind=int_50");
}

void Schedules::getIntindOeisSchedule(const Shell::Property& property, Schedule& quick, Schedule& fallback) {
  // oeisBenchConverted_shuf_4241.txt (fitting to 1/7th of the whole benchmark, that is to 4241 problems)
  // Sub-schedule for 10000Mi strat cap / 10000Mi overall limit
   quick.push("ott+1011_1:1_alpa=false:asg=cautious:drc=off:ins=1:sac=on:sp=unary_frequency:thi=overlap:to=lpo:uwa=interpreted_only:i=492:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_bsr=unit_only:ev=force:ins=1:lcm=reverse:pum=on:sas=z3:spb=goal:ss=included:to=lpo:i=281:si=on:rtra=on_0");
   quick.push("ott+10_1:1_bd=preordered:bsr=on:drc=off:gtg=exists_sym:gtgl=2:ind=int:intindint=infinite:intindsteq=only_one_occurrence:newcnf=on:nwc=3.0:sac=on:sas=z3:sp=const_min:spb=goal:tac=light:thi=all:to=lpo:i=1013:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_asg=cautious:drc=off:fde=unused:gtg=exists_all:ind=both:indoct=on:ins=4:intindstterm=no_skolems:newcnf=on:rawr=on:s2a=on:s2at=5.0:sp=const_min:spb=goal_then_units:tac=rule:to=lpo:i=453:si=on:rtra=on_0");
   quick.push("lrs+1010_4:1_alpa=true:drc=off:fd=preordered:ind=int:indgen=on:indgenss=2:indmd=1:s2a=on:sac=on:sos=on:sp=unary_frequency:to=lpo:i=48:si=on:rtra=on_0");
   quick.push("lrs+1011_1:8_drc=encompass:flr=on:ile=on:ind=int:sp=unary_first:tgt=ground:thi=strong:thitd=on:to=lpo:uhcvi=on:uwa=all:i=322:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_av=off:drc=encompass:ev=force:ind=int:indgen=on:indgenss=1:intindint=infinite:newcnf=on:nwc=5.0:s2a=on:sp=frequency:to=lpo:i=88:si=on:rtra=on_0");
   quick.push("lrs+1010_1:16_bd=off:canc=cautious:fnrw=on:fsr=off:ins=2:newcnf=on:i=61:si=on:rtra=on_0");
   quick.push("lrs+10_1:8_ev=force:fd=preordered:fnrw=on:gtg=exists_all:gtgl=4:newcnf=on:nwc=10.0:sp=const_frequency:tgt=ground:to=lpo:i=125:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_br=off:drc=encompass:fsd=on:gve=force:ind=int:intindint=infinite:kws=inv_precedence:s2a=on:urr=on:uwa=one_side_interpreted:i=30:si=on:rtra=on_0");
   quick.push("lrs+1010_1:3_anc=all:bd=off:canc=cautious:ev=force:fnrw=on:gtg=exists_sym:newcnf=on:nwc=10.0:sac=on:sp=frequency:to=lpo:urr=on:uwa=interpreted_only:i=83:si=on:rtra=on_0");
   quick.push("lrs-10_1:1024_fnrw=on:gtg=position:ins=2:kws=inv_frequency:newcnf=on:norm_ineq=on:sac=on:sas=z3:sos=on:i=401:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_av=off:drc=off:ev=force:fd=preordered:gtg=all:gtgl=4:ind=both:lcm=reverse:s2a=on:sp=reverse_arity:to=lpo:uwa=interpreted_only:i=590:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_av=off:canc=cautious:drc=encompass:ind=int:intindstcomp=none:intindstterm=no_skolems:spb=goal_then_units:to=lpo:urr=on:i=111:si=on:rtra=on_0");
   quick.push("lrs+10_5:1_br=off:canc=force:fd=preordered:ind=int:indc=goal:intindsteq=only_one_occurrence:sos=on:sp=frequency:to=lpo:urr=on:i=24:si=on:rtra=on_0");
   quick.push("ott+10_1:1_br=off:ep=RSTC:ev=force:fnrw=on:gtg=position:ins=1:kws=inv_arity:newcnf=on:sos=all:i=245:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_anc=all:ev=force:fnrw=on:ins=1:newcnf=on:rawr=on:slsq=on:to=lpo:i=119:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_drc=off:ev=force:gtg=all:ind=both:intinddb=on:intindint=finite:intindstcomp=only_one_occurrence:intindstterm=no_skolems:sas=z3:sp=const_min:to=lpo:i=1083:si=on:rtra=on_0");
   quick.push("lrs+10_1:128_br=off:ev=cautious:fd=preordered:fnrw=on:gtg=all:ins=2:kws=precedence:newcnf=on:sos=on:sp=frequency:spb=intro:i=261:si=on:rtra=on_0");
   quick.push("ott+11_1:1_asg=force:av=off:canc=force:drc=off:ev=force:gve=force:ind=both:indc=goal_plus:nwc=3.0:s2a=on:sd=10:sp=const_frequency:ss=included:st=5.0:tar=off:thi=neg_eq:to=lpo:uwa=one_side_constant:i=458:si=on:rtra=on_0");
   quick.push("lrs+11_1:1_drc=encompass:ev=force:fsr=off:kws=precedence:sp=unary_frequency:i=114:si=on:rtra=on_0");
   quick.push("lrs+10_1:128_canc=cautious:drc=encompass:ev=force:fnrw=on:gtg=exists_sym:newcnf=on:nwc=10.0:to=lpo:i=163:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_bd=preordered:br=off:ep=R:fnrw=on:ins=2:newcnf=on:norm_ineq=on:sas=z3:sffsmt=on:to=lpo:i=949:si=on:rtra=on_0");
   quick.push("lrs+1002_1:14_abs=on:br=off:drc=off:fnrw=on:gtg=position:ins=1:kws=inv_arity:newcnf=on:nwc=5.0:sas=z3:tac=light:urr=on:i=180:si=on:rtra=on_0");
   quick.push("ott+1011_1:1_sas=z3:slsq=on:sp=const_min:thi=strong:thitd=on:to=lpo:i=421:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_ep=R:fnrw=on:kws=precedence:newcnf=on:norm_ineq=on:pum=on:sas=z3:sp=frequency:tgt=ground:i=457:si=on:rtra=on_0");
   quick.push("lrs+10_2:1_av=off:canc=cautious:drc=off:ev=force:ind=int:intindsteq=toplevel_not_in_other:nwc=5.0:sos=on:sp=const_frequency:to=lpo:i=31:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_drc=off:fnrw=on:gtg=all:ind=both:intindint=infinite:intindstterm=no_skolems:newcnf=on:s2a=on:sas=z3:sos=on:sp=const_min:tac=axiom:thi=neg_eq:to=lpo:uhcvi=on:i=1409:si=on:rtra=on_0");
  // Improves by expected 768.8930392701382 probs costing 9984 Mi
  // Sub-schedule for 30000Mi strat cap / 30000Mi overall limit
   quick.push("dis+1010_1:8_av=off:bsr=on:ev=cautious:gtg=all:gtgl=5:ind=int:indc=goal_plus:intindsteq=toplevel_not_in_other:nwc=10.0:plsq=on:plsql=on:plsqr=32,1:pum=on:rawr=on:sp=unary_frequency:tac=axiom:taea=off:tgt=ground:thi=strong:thigen=on:uwa=interpreted_only:i=1215:si=on:rtra=on_0");
   quick.push("ott+10_1:1_bd=preordered:bsr=on:drc=off:gtg=exists_sym:gtgl=2:ind=int:intindint=infinite:intindsteq=only_one_occurrence:newcnf=on:nwc=3.0:sac=on:sas=z3:sp=const_min:spb=goal:tac=light:thi=all:to=lpo:i=990:si=on:rtra=on_0");
   quick.push("ott+11_1:1_av=off:canc=force:drc=off:fd=preordered:ind=both:indmd=5:intindsteq=toplevel_not_in_other:pum=on:spb=non_intro:to=lpo:i=1237:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_asg=cautious:drc=off:fde=unused:gtg=exists_all:ind=both:indoct=on:ins=4:intindstterm=no_skolems:newcnf=on:rawr=on:s2a=on:s2at=5.0:sp=const_min:spb=goal_then_units:tac=rule:to=lpo:i=453:si=on:rtra=on_0");
   quick.push("lrs+1010_4:1_alpa=true:drc=off:fd=preordered:ind=int:indgen=on:indgenss=2:indmd=1:s2a=on:sac=on:sos=on:sp=unary_frequency:to=lpo:i=48:si=on:rtra=on_0");
   quick.push("lrs+1011_1:8_drc=encompass:flr=on:ile=on:ind=int:sp=unary_first:tgt=ground:thi=strong:thitd=on:to=lpo:uhcvi=on:uwa=all:i=479:si=on:rtra=on_0");
   quick.push("ott+10_1:16_asg=cautious:drc=off:erd=off:fd=preordered:norm_ineq=on:sp=unary_first:spb=intro:tar=off:tgt=ground:to=lpo:i=711:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_av=off:drc=encompass:ev=force:ind=int:indgen=on:indgenss=1:intindint=infinite:newcnf=on:nwc=5.0:s2a=on:sp=frequency:to=lpo:i=234:si=on:rtra=on_0");
   quick.push("lrs+2_8:1_asg=force:av=off:drc=off:ev=force:flr=on:gtg=all:gtgl=2:ind=both:indmd=10:intindstterm=none:lcm=reverse:nwc=10.0:sp=weighted_frequency:spb=goal:tar=off:tgt=full:thi=strong:thigen=on:to=lpo:i=860:si=on:rtra=on_0");
   quick.push("ott+2_1:1_drc=off:ev=force:fdi=60:ind=int:indao=on:indc=goal:indmd=10:newcnf=on:norm_ineq=on:pum=on:s2agt=16:s2at=1.5:s2pl=no:sp=const_max:spb=goal_then_units:to=lpo:updr=off:uwa=one_side_constant:i=322:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_av=off:drc=off:ev=force:fd=preordered:gtg=all:gtgl=4:ind=both:lcm=reverse:s2a=on:sp=reverse_arity:to=lpo:uwa=interpreted_only:i=872:si=on:rtra=on_0");
   quick.push("ott+21_1:1_canc=cautious:drc=off:gtg=exists_top:ind=both:newcnf=on:spb=goal_then_units:to=lpo:urr=on:i=602:si=on:rtra=on_0");
   quick.push("ott-1011_1:1_bd=off:fsr=off:gtg=exists_sym:gtgl=3:kws=inv_frequency:nwc=10.0:s2a=on:slsq=on:thi=neg_eq:uwa=one_side_interpreted:i=839:si=on:rtra=on_0");
   quick.push("lrs+2_1:128_av=off:drc=off:ev=force:fnrw=on:fsr=off:gtg=all:ind=both:intindstterm=no_skolems:newcnf=on:nwc=5.0:plsq=on:plsqr=2,1:rnwc=on:s2a=on:sp=frequency:spb=goal_then_units:to=lpo:i=641:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_canc=force:fnrw=on:ins=1:newcnf=on:sas=z3:sos=on:sp=frequency:to=lpo:i=1134:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_anc=all:ev=force:fnrw=on:ins=1:newcnf=on:rawr=on:slsq=on:to=lpo:i=671:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_drc=off:ev=force:gtg=all:ind=both:intinddb=on:intindint=finite:intindstcomp=only_one_occurrence:intindstterm=no_skolems:sas=z3:sp=const_min:to=lpo:i=4846:si=on:rtra=on_0");
   quick.push("lrs+10_1:128_br=off:ev=cautious:fd=preordered:fnrw=on:gtg=all:ins=2:kws=precedence:newcnf=on:sos=on:sp=frequency:spb=intro:i=1569:si=on:rtra=on_0");
   quick.push("ott+11_1:1_asg=force:av=off:canc=force:drc=off:ev=force:gve=force:ind=both:indc=goal_plus:nwc=3.0:s2a=on:sd=10:sp=const_frequency:ss=included:st=5.0:tar=off:thi=neg_eq:to=lpo:uwa=one_side_constant:i=3272:si=on:rtra=on_0");
   quick.push("ott+10_1:1_afr=on:asg=cautious:avsq=on:avsqc=1:drc=off:ev=force:ind=int:indc=goal:indu=off:intindstterm=no_skolems:nm=16:spb=non_intro:to=lpo:uwa=all:i=691:si=on:rtra=on_0");
   quick.push("lrs+1011_8:1_afp=5000:afq=1.93:fdi=50:ins=1:pum=on:rawr=on:sas=z3:sos=theory:sp=const_min:spb=goal_then_units:tar=off:tgt=ground:thi=strong:to=lpo:i=618:si=on:rtra=on_0");
   quick.push("lrs+21_8:1_av=off:canc=cautious:drc=encompass:gtg=position:ind=int:intindint=infinite:lwlo=on:plsq=on:plsqc=1:plsqr=8767905,1048576:s2a=on:s2agt=64:s2pl=on:sp=unary_frequency:to=lpo:i=2259:si=on:rtra=on_0");
   quick.push("ott+1010_3:2_canc=force:drc=off:ev=force:gtg=all:ind=both:intindint=infinite:intindstcomp=none:intindstterm=no_skolems:newcnf=on:sos=all:sp=const_max:spb=non_intro:to=lpo:urr=on:i=715:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_ep=R:fnrw=on:kws=precedence:newcnf=on:norm_ineq=on:pum=on:sas=z3:sp=frequency:tgt=ground:i=1603:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_gtg=position:ins=1:norm_ineq=on:sas=z3:sos=on:sp=frequency:thi=all:to=lpo:i=1421:si=on:rtra=on_0");
   quick.push("lrs+10_2:1_av=off:canc=cautious:drc=off:ev=force:ind=int:intindsteq=toplevel_not_in_other:nwc=5.0:sos=on:sp=const_frequency:to=lpo:i=28:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_drc=off:fnrw=on:gtg=all:ind=both:intindint=infinite:intindstterm=no_skolems:newcnf=on:s2a=on:sas=z3:sos=on:sp=const_min:tac=axiom:thi=neg_eq:to=lpo:uhcvi=on:i=1660:si=on:rtra=on_0");
  // Improves by expected 64.39173134160707 probs costing 29963 Mi
  // Sub-schedule for 80000Mi strat cap / 80000Mi overall limit
   quick.push("dis+1010_1:8_av=off:bsr=on:ev=cautious:gtg=all:gtgl=5:ind=int:indc=goal_plus:intindsteq=toplevel_not_in_other:nwc=10.0:plsq=on:plsql=on:plsqr=32,1:pum=on:rawr=on:sp=unary_frequency:tac=axiom:taea=off:tgt=ground:thi=strong:thigen=on:uwa=interpreted_only:i=4823:si=on:rtra=on_0");
   quick.push("ott+1011_1:1_alpa=false:asg=cautious:drc=off:ins=1:sac=on:sp=unary_frequency:thi=overlap:to=lpo:uwa=interpreted_only:i=517:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_asg=cautious:canc=force:ins=1:sas=z3:sos=on:spb=non_intro:tgt=full:to=lpo:i=2189:si=on:rtra=on_0");
   quick.push("ott+10_1:1_bd=preordered:bsr=on:drc=off:gtg=exists_sym:gtgl=2:ind=int:intindint=infinite:intindsteq=only_one_occurrence:newcnf=on:nwc=3.0:sac=on:sas=z3:sp=const_min:spb=goal:tac=light:thi=all:to=lpo:i=990:si=on:rtra=on_0");
   quick.push("ott+11_1:1_av=off:canc=force:drc=off:fd=preordered:ind=both:indmd=5:intindsteq=toplevel_not_in_other:pum=on:spb=non_intro:to=lpo:i=919:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_asg=cautious:drc=off:fde=unused:gtg=exists_all:ind=both:indoct=on:ins=4:intindstterm=no_skolems:newcnf=on:rawr=on:s2a=on:s2at=5.0:sp=const_min:spb=goal_then_units:tac=rule:to=lpo:i=1003:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_ev=force:gtg=all:gtgl=5:nicw=on:sas=z3:sp=const_max:spb=units:to=lpo:i=1667:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_canc=cautious:fsr=off:gs=on:ind=both:intindint=finite:intindsteq=always:intindstterm=none:newcnf=on:s2a=on:s2agt=64:sas=z3:sp=weighted_frequency:tar=off:tgt=ground:thi=all:to=lpo:i=3162:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_asg=cautious:drc=off:gtg=exists_sym:gtgl=5:ind=both:intindint=infinite:intindstcomp=not_in_both:nwc=2.0:sas=z3:sp=frequency:to=lpo:i=2296:si=on:rtra=on_0");
   quick.push("ott+1011_8:1_av=off:drc=off:fde=none:ind=int:kws=inv_arity_squared:plsq=on:plsqc=1:plsqr=9,8:rawr=on:sp=unary_first:tgt=ground:thi=all:uwa=ground:i=1901:si=on:rtra=on_0");
   quick.push("lrs+1011_1:8_drc=encompass:flr=on:ile=on:ind=int:sp=unary_first:tgt=ground:thi=strong:thitd=on:to=lpo:uhcvi=on:uwa=all:i=479:si=on:rtra=on_0");
   quick.push("ott+10_1:16_asg=cautious:drc=off:erd=off:fd=preordered:norm_ineq=on:sp=unary_first:spb=intro:tar=off:tgt=ground:to=lpo:i=2617:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_avsq=on:avsqr=6,31:drc=off:ins=3:newcnf=on:nm=16:s2a=on:sas=z3:sp=frequency:tac=rule:thi=all:to=lpo:uwa=ground:i=795:si=on:rtra=on_0");
   quick.push("lrs+1_1:256_awrs=decay:awrsf=20:ind=struct:indc=goal_plus:ins=2:nm=40:nwc=6.0:s2at=3.0:slsq=on:slsql=off:slsqr=11,17:spb=non_intro:thi=all:thitd=on:to=lpo:i=1803:si=on:rtra=on_0");
   quick.push("ott+1002_5:2_canc=cautious:fd=preordered:gsp=on:gtg=exists_all:gtgl=3:ind=both:s2a=on:s2at=5.0:sac=on:sas=z3:slsq=on:slsqc=4:slsqr=1,4:sp=reverse_arity:to=lpo:urr=on:i=2346:si=on:rtra=on_0");
   quick.push("lrs-10_1:1024_fnrw=on:gtg=position:ins=2:kws=inv_frequency:newcnf=on:norm_ineq=on:sac=on:sas=z3:sos=on:i=1399:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_av=off:drc=off:ev=force:fd=preordered:gtg=all:gtgl=4:ind=both:lcm=reverse:s2a=on:sp=reverse_arity:to=lpo:uwa=interpreted_only:i=1549:si=on:rtra=on_0");
   quick.push("lrs+1011_1:128_afp=100000:afq=1.9:avsq=on:canc=cautious:ev=force:fde=none:flr=on:fnrw=on:fsr=off:gtg=position:newcnf=on:sas=z3:sp=unary_first:spb=non_intro:thi=neg_eq:i=1374:si=on:rtra=on_0");
   quick.push("ott+21_1:1_canc=cautious:drc=off:gtg=exists_top:ind=both:newcnf=on:spb=goal_then_units:to=lpo:urr=on:i=739:si=on:rtra=on_0");
   quick.push("ott-1011_1:1_bd=off:fsr=off:gtg=exists_sym:gtgl=3:kws=inv_frequency:nwc=10.0:s2a=on:slsq=on:thi=neg_eq:uwa=one_side_interpreted:i=1101:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_canc=force:fnrw=on:ins=1:newcnf=on:sas=z3:sos=on:sp=frequency:to=lpo:i=2335:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_drc=off:ev=force:gtg=all:ind=both:intinddb=on:intindint=finite:intindstcomp=only_one_occurrence:intindstterm=no_skolems:sas=z3:sp=const_min:to=lpo:i=11689:si=on:rtra=on_0");
   quick.push("ott+11_1:1_asg=force:av=off:canc=force:drc=off:ev=force:gve=force:ind=both:indc=goal_plus:nwc=3.0:s2a=on:sd=10:sp=const_frequency:ss=included:st=5.0:tar=off:thi=neg_eq:to=lpo:uwa=one_side_constant:i=7199:si=on:rtra=on_0");
   quick.push("ott+10_1:1_afr=on:asg=cautious:avsq=on:avsqc=1:drc=off:ev=force:ind=int:indc=goal:indu=off:intindstterm=no_skolems:nm=16:spb=non_intro:to=lpo:uwa=all:i=691:si=on:rtra=on_0");
   quick.push("lrs+21_8:1_av=off:canc=cautious:drc=encompass:gtg=position:ind=int:intindint=infinite:lwlo=on:plsq=on:plsqc=1:plsqr=8767905,1048576:s2a=on:s2agt=64:s2pl=on:sp=unary_frequency:to=lpo:i=2259:si=on:rtra=on_0");
   quick.push("ott+1010_3:2_canc=force:drc=off:ev=force:gtg=all:ind=both:intindint=infinite:intindstcomp=none:intindstterm=no_skolems:newcnf=on:sos=all:sp=const_max:spb=non_intro:to=lpo:urr=on:i=1455:si=on:rtra=on_0");
   quick.push("ott+10_1:1_ind=both:indc=goal:intindsteq=not_in_both:nwc=3.0:sas=z3:sp=frequency:to=lpo:i=306:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_ep=R:fnrw=on:kws=precedence:newcnf=on:norm_ineq=on:pum=on:sas=z3:sp=frequency:tgt=ground:i=11267:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_drc=off:fnrw=on:gtg=all:ind=both:intindint=infinite:intindstterm=no_skolems:newcnf=on:s2a=on:sas=z3:sos=on:sp=const_min:tac=axiom:thi=neg_eq:to=lpo:uhcvi=on:i=8399:si=on:rtra=on_0");
  // Improves by expected 38.96337376225668 probs costing 79240 Mi
  // Sub-schedule for 120000Mi strat cap / 120000Mi overall limit
   quick.push("dis+1010_1:8_av=off:bsr=on:ev=cautious:gtg=all:gtgl=5:ind=int:indc=goal_plus:intindsteq=toplevel_not_in_other:nwc=10.0:plsq=on:plsql=on:plsqr=32,1:pum=on:rawr=on:sp=unary_frequency:tac=axiom:taea=off:tgt=ground:thi=strong:thigen=on:uwa=interpreted_only:i=1215:si=on:rtra=on_0");
   quick.push("ott+1011_1:1_alpa=false:asg=cautious:drc=off:ins=1:sac=on:sp=unary_frequency:thi=overlap:to=lpo:uwa=interpreted_only:i=376:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_asg=cautious:canc=force:ins=1:sas=z3:sos=on:spb=non_intro:tgt=full:to=lpo:i=2189:si=on:rtra=on_0");
   quick.push("ott+10_1:1_bd=preordered:bsr=on:drc=off:gtg=exists_sym:gtgl=2:ind=int:intindint=infinite:intindsteq=only_one_occurrence:newcnf=on:nwc=3.0:sac=on:sas=z3:sp=const_min:spb=goal:tac=light:thi=all:to=lpo:i=6179:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_asg=cautious:drc=off:fde=unused:gtg=exists_all:ind=both:indoct=on:ins=4:intindstterm=no_skolems:newcnf=on:rawr=on:s2a=on:s2at=5.0:sp=const_min:spb=goal_then_units:tac=rule:to=lpo:i=3437:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_ev=force:gtg=all:gtgl=5:nicw=on:sas=z3:sp=const_max:spb=units:to=lpo:i=1667:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_canc=cautious:fsr=off:gs=on:ind=both:intindint=finite:intindsteq=always:intindstterm=none:newcnf=on:s2a=on:s2agt=64:sas=z3:sp=weighted_frequency:tar=off:tgt=ground:thi=all:to=lpo:i=2504:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_asg=cautious:drc=off:gtg=exists_sym:gtgl=5:ind=both:intindint=infinite:intindstcomp=not_in_both:nwc=2.0:sas=z3:sp=frequency:to=lpo:i=2296:si=on:rtra=on_0");
   quick.push("lrs+1011_1:8_drc=encompass:flr=on:ile=on:ind=int:sp=unary_first:tgt=ground:thi=strong:thitd=on:to=lpo:uhcvi=on:uwa=all:i=479:si=on:rtra=on_0");
   quick.push("ott+10_1:16_asg=cautious:drc=off:erd=off:fd=preordered:norm_ineq=on:sp=unary_first:spb=intro:tar=off:tgt=ground:to=lpo:i=2617:si=on:rtra=on_0");
   quick.push("lrs+2_16:1_aac=none:amm=off:canc=cautious:ind=both:indao=on:intindsteq=not_in_both:intindstterm=none:s2a=on:sp=weighted_frequency:spb=goal:thi=overlap:thitd=on:to=lpo:urr=on:i=4483:si=on:rtra=on_0");
   quick.push("lrs+2_8:1_asg=force:av=off:drc=off:ev=force:flr=on:gtg=all:gtgl=2:ind=both:indmd=10:intindstterm=none:lcm=reverse:nwc=10.0:sp=weighted_frequency:spb=goal:tar=off:tgt=full:thi=strong:thigen=on:to=lpo:i=27972:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_avsq=on:avsqr=6,31:drc=off:ins=3:newcnf=on:nm=16:s2a=on:sas=z3:sp=frequency:tac=rule:thi=all:to=lpo:uwa=ground:i=795:si=on:rtra=on_0");
   quick.push("ott+1002_5:2_canc=cautious:fd=preordered:gsp=on:gtg=exists_all:gtgl=3:ind=both:s2a=on:s2at=5.0:sac=on:sas=z3:slsq=on:slsqc=4:slsqr=1,4:sp=reverse_arity:to=lpo:urr=on:i=6638:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_av=off:drc=off:ev=force:fd=preordered:gtg=all:gtgl=4:ind=both:lcm=reverse:s2a=on:sp=reverse_arity:to=lpo:uwa=interpreted_only:i=872:si=on:rtra=on_0");
   quick.push("lrs+1011_1:128_afp=100000:afq=1.9:avsq=on:canc=cautious:ev=force:fde=none:flr=on:fnrw=on:fsr=off:gtg=position:newcnf=on:sas=z3:sp=unary_first:spb=non_intro:thi=neg_eq:i=1374:si=on:rtra=on_0");
   quick.push("ott+21_1:1_canc=cautious:drc=off:gtg=exists_top:ind=both:newcnf=on:spb=goal_then_units:to=lpo:urr=on:i=739:si=on:rtra=on_0");
   quick.push("ott-1011_1:1_bd=off:fsr=off:gtg=exists_sym:gtgl=3:kws=inv_frequency:nwc=10.0:s2a=on:slsq=on:thi=neg_eq:uwa=one_side_interpreted:i=1101:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_canc=force:fnrw=on:ins=1:newcnf=on:sas=z3:sos=on:sp=frequency:to=lpo:i=2335:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_drc=off:ev=force:gtg=all:ind=both:intinddb=on:intindint=finite:intindstcomp=only_one_occurrence:intindstterm=no_skolems:sas=z3:sp=const_min:to=lpo:i=25013:si=on:rtra=on_0");
   quick.push("ott+10_1:1_afr=on:asg=cautious:avsq=on:avsqc=1:drc=off:ev=force:ind=int:indc=goal:indu=off:intindstterm=no_skolems:nm=16:spb=non_intro:to=lpo:uwa=all:i=691:si=on:rtra=on_0");
   quick.push("lrs+1011_8:1_afp=5000:afq=1.93:fdi=50:ins=1:pum=on:rawr=on:sas=z3:sos=theory:sp=const_min:spb=goal_then_units:tar=off:tgt=ground:thi=strong:to=lpo:i=989:si=on:rtra=on_0");
   quick.push("lrs+21_8:1_av=off:canc=cautious:drc=encompass:gtg=position:ind=int:intindint=infinite:lwlo=on:plsq=on:plsqc=1:plsqr=8767905,1048576:s2a=on:s2agt=64:s2pl=on:sp=unary_frequency:to=lpo:i=2259:si=on:rtra=on_0");
   quick.push("ott+1010_3:2_canc=force:drc=off:ev=force:gtg=all:ind=both:intindint=infinite:intindstcomp=none:intindstterm=no_skolems:newcnf=on:sos=all:sp=const_max:spb=non_intro:to=lpo:urr=on:i=1455:si=on:rtra=on_0");
   quick.push("ott+10_1:1_ind=both:indc=goal:intindsteq=not_in_both:nwc=3.0:sas=z3:sp=frequency:to=lpo:i=306:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_ep=R:fnrw=on:kws=precedence:newcnf=on:norm_ineq=on:pum=on:sas=z3:sp=frequency:tgt=ground:i=17601:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_gtg=position:ins=1:norm_ineq=on:sas=z3:sos=on:sp=frequency:thi=all:to=lpo:i=1642:si=on:rtra=on_0");
  // Improves by expected 20.483810176123523 probs costing 119197 Mi
  // Sub-schedule for 120000Mi strat cap / 120000Mi overall limit
   quick.push("dis+1010_1:8_av=off:bsr=on:ev=cautious:gtg=all:gtgl=5:ind=int:indc=goal_plus:intindsteq=toplevel_not_in_other:nwc=10.0:plsq=on:plsql=on:plsqr=32,1:pum=on:rawr=on:sp=unary_frequency:tac=axiom:taea=off:tgt=ground:thi=strong:thigen=on:uwa=interpreted_only:i=5153:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_asg=cautious:canc=force:ins=1:sas=z3:sos=on:spb=non_intro:tgt=full:to=lpo:i=2189:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_canc=cautious:fsr=off:gs=on:ind=both:intindint=finite:intindsteq=always:intindstterm=none:newcnf=on:s2a=on:s2agt=64:sas=z3:sp=weighted_frequency:tar=off:tgt=ground:thi=all:to=lpo:i=2504:si=on:rtra=on_0");
   quick.push("ott+1011_8:1_av=off:drc=off:fde=none:ind=int:kws=inv_arity_squared:plsq=on:plsqc=1:plsqr=9,8:rawr=on:sp=unary_first:tgt=ground:thi=all:uwa=ground:i=1901:si=on:rtra=on_0");
   quick.push("lrs+2_16:1_aac=none:amm=off:canc=cautious:ind=both:indao=on:intindsteq=not_in_both:intindstterm=none:s2a=on:sp=weighted_frequency:spb=goal:thi=overlap:thitd=on:to=lpo:urr=on:i=27251:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_avsq=on:avsqr=6,31:drc=off:ins=3:newcnf=on:nm=16:s2a=on:sas=z3:sp=frequency:tac=rule:thi=all:to=lpo:uwa=ground:i=795:si=on:rtra=on_0");
   quick.push("ott+1002_5:2_canc=cautious:fd=preordered:gsp=on:gtg=exists_all:gtgl=3:ind=both:s2a=on:s2at=5.0:sac=on:sas=z3:slsq=on:slsqc=4:slsqr=1,4:sp=reverse_arity:to=lpo:urr=on:i=2551:si=on:rtra=on_0");
   quick.push("lrs+1011_1:128_afp=100000:afq=1.9:avsq=on:canc=cautious:ev=force:fde=none:flr=on:fnrw=on:fsr=off:gtg=position:newcnf=on:sas=z3:sp=unary_first:spb=non_intro:thi=neg_eq:i=1374:si=on:rtra=on_0");
   quick.push("ott+21_1:1_canc=cautious:drc=off:gtg=exists_top:ind=both:newcnf=on:spb=goal_then_units:to=lpo:urr=on:i=739:si=on:rtra=on_0");
   quick.push("ott-1011_1:1_bd=off:fsr=off:gtg=exists_sym:gtgl=3:kws=inv_frequency:nwc=10.0:s2a=on:slsq=on:thi=neg_eq:uwa=one_side_interpreted:i=1101:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_canc=force:fnrw=on:ins=1:newcnf=on:sas=z3:sos=on:sp=frequency:to=lpo:i=2097:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_drc=off:ev=force:gtg=all:ind=both:intinddb=on:intindint=finite:intindstcomp=only_one_occurrence:intindstterm=no_skolems:sas=z3:sp=const_min:to=lpo:i=25013:si=on:rtra=on_0");
   quick.push("ott+21_6:1_avsq=on:avsql=on:gtg=position:gtgl=3:ind=int:intindsteq=not_in_both:nm=10:pum=on:sas=z3:sp=const_min:thi=all:thigen=on:to=lpo:uwa=ground:i=11432:si=on:rtra=on_0");
   quick.push("lrs+10_1:128_br=off:ev=cautious:fd=preordered:fnrw=on:gtg=all:ins=2:kws=precedence:newcnf=on:sos=on:sp=frequency:spb=intro:i=20153:si=on:rtra=on_0");
   quick.push("ott+11_1:1_asg=force:av=off:canc=force:drc=off:ev=force:gve=force:ind=both:indc=goal_plus:nwc=3.0:s2a=on:sd=10:sp=const_frequency:ss=included:st=5.0:tar=off:thi=neg_eq:to=lpo:uwa=one_side_constant:i=2538:si=on:rtra=on_0");
   quick.push("ott+10_1:1_afr=on:asg=cautious:avsq=on:avsqc=1:drc=off:ev=force:ind=int:indc=goal:indu=off:intindstterm=no_skolems:nm=16:spb=non_intro:to=lpo:uwa=all:i=691:si=on:rtra=on_0");
   quick.push("lrs+21_8:1_av=off:canc=cautious:drc=encompass:gtg=position:ind=int:intindint=infinite:lwlo=on:plsq=on:plsqc=1:plsqr=8767905,1048576:s2a=on:s2agt=64:s2pl=on:sp=unary_frequency:to=lpo:i=2259:si=on:rtra=on_0");
   quick.push("ott+1010_3:2_canc=force:drc=off:ev=force:gtg=all:ind=both:intindint=infinite:intindstcomp=none:intindstterm=no_skolems:newcnf=on:sos=all:sp=const_max:spb=non_intro:to=lpo:urr=on:i=1455:si=on:rtra=on_0");
   quick.push("ott+10_1:1_ind=both:indc=goal:intindsteq=not_in_both:nwc=3.0:sas=z3:sp=frequency:to=lpo:i=306:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_drc=off:fnrw=on:gtg=all:ind=both:intindint=infinite:intindstterm=no_skolems:newcnf=on:s2a=on:sas=z3:sos=on:sp=const_min:tac=axiom:thi=neg_eq:to=lpo:uhcvi=on:i=8399:si=on:rtra=on_0");
  // Improves by expected 11.98641809031958 probs costing 119881 Mi
  // Sub-schedule for 120000Mi strat cap / 120000Mi overall limit
   quick.push("dis+1010_1:8_av=off:bsr=on:ev=cautious:gtg=all:gtgl=5:ind=int:indc=goal_plus:intindsteq=toplevel_not_in_other:nwc=10.0:plsq=on:plsql=on:plsqr=32,1:pum=on:rawr=on:sp=unary_frequency:tac=axiom:taea=off:tgt=ground:thi=strong:thigen=on:uwa=interpreted_only:i=5153:si=on:rtra=on_0");
   quick.push("ott+10_1:1_bd=preordered:bsr=on:drc=off:gtg=exists_sym:gtgl=2:ind=int:intindint=infinite:intindsteq=only_one_occurrence:newcnf=on:nwc=3.0:sac=on:sas=z3:sp=const_min:spb=goal:tac=light:thi=all:to=lpo:i=8390:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_ev=force:gtg=all:gtgl=5:nicw=on:sas=z3:sp=const_max:spb=units:to=lpo:i=1667:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_canc=cautious:fsr=off:gs=on:ind=both:intindint=finite:intindsteq=always:intindstterm=none:newcnf=on:s2a=on:s2agt=64:sas=z3:sp=weighted_frequency:tar=off:tgt=ground:thi=all:to=lpo:i=2330:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_asg=cautious:drc=off:gtg=exists_sym:gtgl=5:ind=both:intindint=infinite:intindstcomp=not_in_both:nwc=2.0:sas=z3:sp=frequency:to=lpo:i=3525:si=on:rtra=on_0");
   quick.push("lrs+1011_1:8_drc=encompass:flr=on:ile=on:ind=int:sp=unary_first:tgt=ground:thi=strong:thitd=on:to=lpo:uhcvi=on:uwa=all:i=2083:si=on:rtra=on_0");
   quick.push("ott+10_1:16_asg=cautious:drc=off:erd=off:fd=preordered:norm_ineq=on:sp=unary_first:spb=intro:tar=off:tgt=ground:to=lpo:i=2617:si=on:rtra=on_0");
   quick.push("lrs+2_16:1_aac=none:amm=off:canc=cautious:ind=both:indao=on:intindsteq=not_in_both:intindstterm=none:s2a=on:sp=weighted_frequency:spb=goal:thi=overlap:thitd=on:to=lpo:urr=on:i=4369:si=on:rtra=on_0");
   quick.push("ott+1002_5:2_canc=cautious:fd=preordered:gsp=on:gtg=exists_all:gtgl=3:ind=both:s2a=on:s2at=5.0:sac=on:sas=z3:slsq=on:slsqc=4:slsqr=1,4:sp=reverse_arity:to=lpo:urr=on:i=2346:si=on:rtra=on_0");
   quick.push("lrs-10_1:1024_fnrw=on:gtg=position:ins=2:kws=inv_frequency:newcnf=on:norm_ineq=on:sac=on:sas=z3:sos=on:i=43082:si=on:rtra=on_0");
   quick.push("ott+21_1:1_canc=cautious:drc=off:gtg=exists_top:ind=both:newcnf=on:spb=goal_then_units:to=lpo:urr=on:i=739:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_canc=force:fnrw=on:ins=1:newcnf=on:sas=z3:sos=on:sp=frequency:to=lpo:i=1134:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_drc=off:ev=force:gtg=all:ind=both:intinddb=on:intindint=finite:intindstcomp=only_one_occurrence:intindstterm=no_skolems:sas=z3:sp=const_min:to=lpo:i=25013:si=on:rtra=on_0");
   quick.push("ott+11_1:1_asg=force:av=off:canc=force:drc=off:ev=force:gve=force:ind=both:indc=goal_plus:nwc=3.0:s2a=on:sd=10:sp=const_frequency:ss=included:st=5.0:tar=off:thi=neg_eq:to=lpo:uwa=one_side_constant:i=3272:si=on:rtra=on_0");
   quick.push("ott+10_1:1_afr=on:asg=cautious:avsq=on:avsqc=1:drc=off:ev=force:ind=int:indc=goal:indu=off:intindstterm=no_skolems:nm=16:spb=non_intro:to=lpo:uwa=all:i=691:si=on:rtra=on_0");
   quick.push("lrs+21_8:1_av=off:canc=cautious:drc=encompass:gtg=position:ind=int:intindint=infinite:lwlo=on:plsq=on:plsqc=1:plsqr=8767905,1048576:s2a=on:s2agt=64:s2pl=on:sp=unary_frequency:to=lpo:i=2259:si=on:rtra=on_0");
   quick.push("ott+10_1:1_ind=both:indc=goal:intindsteq=not_in_both:nwc=3.0:sas=z3:sp=frequency:to=lpo:i=1019:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_gtg=position:ins=1:norm_ineq=on:sas=z3:sos=on:sp=frequency:thi=all:to=lpo:i=1642:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_drc=off:fnrw=on:gtg=all:ind=both:intindint=infinite:intindstterm=no_skolems:newcnf=on:s2a=on:sas=z3:sos=on:sp=const_min:tac=axiom:thi=neg_eq:to=lpo:uhcvi=on:i=8399:si=on:rtra=on_0");
  // Improves by expected 8.168250634990825 probs costing 119711 Mi
  // Sub-schedule for 120000Mi strat cap / 120000Mi overall limit
   quick.push("dis+1010_1:8_av=off:bsr=on:ev=cautious:gtg=all:gtgl=5:ind=int:indc=goal_plus:intindsteq=toplevel_not_in_other:nwc=10.0:plsq=on:plsql=on:plsqr=32,1:pum=on:rawr=on:sp=unary_frequency:tac=axiom:taea=off:tgt=ground:thi=strong:thigen=on:uwa=interpreted_only:i=5153:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_asg=cautious:drc=off:fde=unused:gtg=exists_all:ind=both:indoct=on:ins=4:intindstterm=no_skolems:newcnf=on:rawr=on:s2a=on:s2at=5.0:sp=const_min:spb=goal_then_units:tac=rule:to=lpo:i=3801:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_asg=cautious:drc=off:gtg=exists_sym:gtgl=5:ind=both:intindint=infinite:intindstcomp=not_in_both:nwc=2.0:sas=z3:sp=frequency:to=lpo:i=3525:si=on:rtra=on_0");
   quick.push("lrs+2_16:1_aac=none:amm=off:canc=cautious:ind=both:indao=on:intindsteq=not_in_both:intindstterm=none:s2a=on:sp=weighted_frequency:spb=goal:thi=overlap:thitd=on:to=lpo:urr=on:i=27251:si=on:rtra=on_0");
   quick.push("ott+1002_5:2_canc=cautious:fd=preordered:gsp=on:gtg=exists_all:gtgl=3:ind=both:s2a=on:s2at=5.0:sac=on:sas=z3:slsq=on:slsqc=4:slsqr=1,4:sp=reverse_arity:to=lpo:urr=on:i=8845:si=on:rtra=on_0");
   quick.push("lrs-10_1:1024_fnrw=on:gtg=position:ins=2:kws=inv_frequency:newcnf=on:norm_ineq=on:sac=on:sas=z3:sos=on:i=22775:si=on:rtra=on_0");
   quick.push("ott+21_1:1_canc=cautious:drc=off:gtg=exists_top:ind=both:newcnf=on:spb=goal_then_units:to=lpo:urr=on:i=739:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_canc=force:fnrw=on:ins=1:newcnf=on:sas=z3:sos=on:sp=frequency:to=lpo:i=3187:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_drc=off:ev=force:gtg=all:ind=both:intinddb=on:intindint=finite:intindstcomp=only_one_occurrence:intindstterm=no_skolems:sas=z3:sp=const_min:to=lpo:i=25013:si=on:rtra=on_0");
   quick.push("ott+21_6:1_avsq=on:avsql=on:gtg=position:gtgl=3:ind=int:intindsteq=not_in_both:nm=10:pum=on:sas=z3:sp=const_min:thi=all:thigen=on:to=lpo:uwa=ground:i=12063:si=on:rtra=on_0");
   quick.push("ott+11_1:1_asg=force:av=off:canc=force:drc=off:ev=force:gve=force:ind=both:indc=goal_plus:nwc=3.0:s2a=on:sd=10:sp=const_frequency:ss=included:st=5.0:tar=off:thi=neg_eq:to=lpo:uwa=one_side_constant:i=2799:si=on:rtra=on_0");
   quick.push("ott+10_1:1_afr=on:asg=cautious:avsq=on:avsqc=1:drc=off:ev=force:ind=int:indc=goal:indu=off:intindstterm=no_skolems:nm=16:spb=non_intro:to=lpo:uwa=all:i=691:si=on:rtra=on_0");
  // Improves by expected 5.072521477354672 probs costing 115830 Mi
  // Overall score 917.9591447527905 probs on average / budget 593806 Mi
}

// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------

// insertionsort/mset/conjecture:       lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:sos=theory:sstl=1:sp=occurrence:indao=on_89
// insertionsort/mset/lemma1:           lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:sos=theory:sstl=1:sp=occurrence:indao=on_89
//
// insertionsort/sortedness/conjecture: lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:sos=theory:sstl=1:sp=occurrence:indao=on_89
// insertionsort/sortedness/lemma1:     lrs+1002_1_aac=none:anc=all:sac=on:ind=struct:thsq=on:to=lpo:nui=on:drc=encompass:sik=recursion:urr=on_89
//
// mergesort/mset/conjecture:           lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:thsq=on:sp=occurrence_89
// mergesort/mset/lemma1:               ???
// mergesort/mset/lemma2:               lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:thsq=on:sp=occurrence_89
// mergesort/mset/lemma3:               lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:thsq=on:sp=occurrence_89
//
// mergesort/sortedness/conjecture:     lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:thsq=on:sp=occurrence_89
// mergesort/sortedness/lemma1:         ???
// mergesort/sortedness/lemma2:         lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:thsq=on:sp=occurrence:nui=on_89
//
// quicksort/mset/conjecture:           lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:sos=theory:sstl=1:sp=occurrence:indao=on_89
// quicksort/mset/lemma1:               lrs+10_1_drc=encompass:ind=struct:sik=one:to=lpo:thsq=on:sp=occurrence_89
// quicksort/mset/lemma2:               lrs+10_1_drc=encompass:ind=struct:sik=one:to=lpo:sos=theory:sstl=1:sp=occurrence:indao=on_89
//
// quicksort/sortedness/conjecture:     lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:thsq=on:sp=occurrence_89
// quicksort/sortedness/lemma1:         lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:thsq=on:sp=occurrence:nui=on_89
// quicksort/sortedness/lemma2:         lrs+10_1_drc=encompass:ind=struct:sik=one:to=lpo:thsq=on:sp=occurrence_89
// quicksort/sortedness/lemma3:         lrs+10_1_drc=encompass:ind=struct:sik=one:to=lpo:thsq=on:sp=occurrence:indao=on_100
// quicksort/sortedness/lemma4:         lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:thsq=on:sp=occurrence:nui=on:indao=on_89
// quicksort/sortedness/lemma5:         lrs+10_1_ind=struct:sos=theory:sstl=1:urr=on:nui=on:indao=on:sik=recursion:drc=encompass_89
// quicksort/sortedness/lemma6:         lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:thsq=on:sp=occurrence:nui=on:indao=on_89
// quicksort/sortedness/lemma7:         lrs+10_1_drc=encompass:ind=struct:sik=one:to=lpo:thsq=on:sp=occurrence:indao=on:nui=on_89

void Schedules::getStructInductionSchedule(const Shell::Property& property, Schedule& quick, Schedule& fallback) {
  // Ran on all_fair.txt
  // Sub-schedule for 2000Mi strat cap / 2000Mi overall limit
   quick.push("ott+10_1:4_av=off:drc=off:ind=struct:indgen=on:newcnf=on:nui=on:uwa=ground:i=10:si=on:rtra=on_0");
   quick.push("dis+10_1:1_aac=none:alpa=true:drc=off:ind=both:indoct=on:newcnf=on:sac=on:taea=off:to=lpo:i=5:si=on:rtra=on_0");
   quick.push("lrs+1010_1:3_drc=encompass:ind=both:indmd=1:nui=on:s2a=on:ss=axioms:i=24:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_bd=off:gtg=exists_top:ind=struct:indmd=2:indstrhyp=on:nwc=5.0:s2a=on:s2agt=16:i=36:si=on:rtra=on_0");
   quick.push("ott+10_1:32_bsd=on:canc=force:drc=off:fsr=off:ind=struct:indao=on:newcnf=on:rawr=on:sac=on:taea=off:i=284:si=on:rtra=on_0");
   quick.push("lrs+1011_5:1_av=off:canc=force:drc=encompass:s2a=on:sp=const_frequency:to=lpo:urr=on:i=7:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_atotf=0.2:drc=off:gtg=exists_top:ind=both:nwc=10.0:sac=on:sp=unary_frequency:tgt=ground:to=lpo:i=7:si=on:rtra=on_0");
   quick.push("dis+10_1:1_gtg=exists_top:gve=cautious:ind=struct:indn=off:rawr=on:s2a=on:s2agt=8:sac=on:uwa=all:i=11:si=on:rtra=on_0");
   quick.push("lrs+2_1:4_drc=off:gtg=position:gve=cautious:ile=on:ind=struct:indao=on:indc=goal:indmd=6:newcnf=on:nwc=5.0:s2a=on:tac=axiom:to=lpo:i=232:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_drc=off:ind=both:indoct=on:indstrhyp=on:sos=on:sp=const_frequency:ss=axioms:to=lpo:i=96:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bce=on:drc=off:fsd=on:ind=struct:indgen=on:indgenss=2:sac=on:taea=off:to=lpo:uwa=interpreted_only:i=293:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_avsq=on:avsqc=1:avsqr=1,16:drc=off:ev=force:ind=struct:sos=on:to=lpo:urr=on:i=14:si=on:rtra=on_0");
   quick.push("ott+10_1:172_awrs=decay:drc=off:gtg=position:ind=both:indao=on:indc=goal:indgen=on:newcnf=on:sik=recursion:sp=weighted_frequency:taea=off:uhcvi=on:i=165:si=on:rtra=on_0");
   quick.push("dis+10_1:14_gtg=position:sp=frequency:ss=axioms:tgt=full:i=9:si=on:rtra=on_0");
   quick.push("lrs+10_1:128_drc=off:gtg=exists_top:ind=struct:indstrhyp=on:sac=on:slsq=on:slsqc=1:taea=off:i=25:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_av=off:br=off:drc=off:gtg=exists_all:ind=both:indc=goal:indmd=15:plsq=on:plsqr=9,1:sos=on:sp=unary_frequency:tgt=ground:to=lpo:uace=off:uwa=one_side_interpreted:i=3:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_drc=encompass:ind=struct:indao=on:newcnf=on:plsq=on:plsqr=32,1:sp=frequency:to=lpo:i=2:si=on:rtra=on_0");
   quick.push("dis+1002_1:1024_av=off:bd=off:drc=off:fsr=off:gtg=position:ind=struct:indc=goal:indgen=on:indgenss=2:taea=off:to=lpo:i=742:si=on:rtra=on_0");
   quick.push("lrs+1010_1:128_aac=none:alpa=false:cond=fast:drc=off:gtg=position:gve=cautious:ind=both:norm_ineq=on:nwc=10.0:sac=on:sp=frequency:tgt=full:to=lpo:i=53:si=on:rtra=on_0");
  // Improves by expected 5526.94623336456 probs costing 1999 Mi
  // Sub-schedule for 4000Mi strat cap / 4000Mi overall limit
   quick.push("lrs+1010_1:3_drc=encompass:ind=both:indmd=1:nui=on:s2a=on:ss=axioms:i=66:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_drc=encompass:fsr=off:ind=struct:indao=on:indmd=3:indoct=on:newcnf=on:taea=off:i=51:si=on:rtra=on_0");
   quick.push("ott+11_5:1_av=off:br=off:canc=cautious:drc=off:ev=cautious:fsr=off:ind=struct:indstrhyp=on:newcnf=on:i=128:si=on:rtra=on_0");
   quick.push("ott+10_1:12_bsd=on:drc=off:fde=none:ind=struct:indgen=on:indgenss=2:norm_ineq=on:sac=on:taea=off:thi=strong:uwa=ground:i=571:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_alpa=random:drc=encompass:gtg=all:kws=arity:nwc=3.0:spb=goal_then_units:ss=axioms:urr=on:i=44:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_fsr=off:gtg=position:ind=both:indmd=1:indstrhyp=on:nwc=5.0:s2a=on:i=31:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_bsr=unit_only:ev=cautious:ind=both:nui=on:sac=on:i=47:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bsd=on:drc=off:fd=preordered:ind=struct:indao=on:indgenss=7:kws=inv_arity:rawr=on:sac=on:sp=const_max:spb=intro:sup=off:uhcvi=on:updr=off:uwa=ground:i=380:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bce=on:drc=off:fsd=on:ind=struct:indgen=on:indgenss=2:sac=on:taea=off:to=lpo:uwa=interpreted_only:i=860:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_avsq=on:avsqc=1:avsqr=1,16:drc=off:ev=force:ind=struct:sos=on:to=lpo:urr=on:i=46:si=on:rtra=on_0");
   quick.push("ott+10_1:172_awrs=decay:drc=off:gtg=position:ind=both:indao=on:indc=goal:indgen=on:newcnf=on:sik=recursion:sp=weighted_frequency:taea=off:uhcvi=on:i=1108:si=on:rtra=on_0");
   quick.push("lrs+10_1:128_drc=off:gtg=exists_top:ind=struct:indstrhyp=on:sac=on:slsq=on:slsqc=1:taea=off:i=61:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_drc=off:gtg=exists_sym:ind=struct:indstrhyp=on:sp=const_min:taea=off:tar=off:to=lpo:i=67:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_av=off:br=off:drc=off:gtg=exists_all:ind=both:indc=goal:indmd=15:plsq=on:plsqr=9,1:sos=on:sp=unary_frequency:tgt=ground:to=lpo:uace=off:uwa=one_side_interpreted:i=3:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_av=off:ind=struct:newcnf=on:plsq=on:plsqc=1:plsqr=32,1:rawr=on:sos=all:sup=off:i=20:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_drc=encompass:ind=struct:indao=on:newcnf=on:plsq=on:plsqr=32,1:sp=frequency:to=lpo:i=19:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_av=off:drc=off:gtg=position:ind=struct:indoct=on:plsq=on:plsqc=1:plsqr=32,1:to=lpo:i=33:si=on:rtra=on_0");
   quick.push("ott+21_1:10_bsr=on:canc=force:drc=encompass:ev=cautious:ile=on:ind=struct:indao=on:indoct=on:newcnf=on:spb=non_intro:tac=rule:taea=off:to=lpo:i=443:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_bd=preordered:gtg=exists_all:gtgl=3:ind=struct:indmd=1:indstrhyp=on:nui=on:sos=on:i=18:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_canc=cautious:sos=on:sp=unary_frequency:i=19:si=on:rtra=on_0");
  // Improves by expected 305.621133946607 probs costing 3995 Mi
  // Sub-schedule for 4000Mi strat cap / 4000Mi overall limit
   quick.push("lrs+10_1:1_gtg=exists_sym:ind=struct:indstrhyp=on:kws=precedence:sos=on:sp=unary_first:spb=goal:urr=on:i=89:si=on:rtra=on_0");
   quick.push("ott+10_1:1_ev=cautious:gtg=exists_top:ind=struct:indc=goal:indstrhyp=on:nwc=10.0:sos=on:i=72:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_bd=off:gtg=exists_top:ind=struct:indmd=2:indstrhyp=on:nwc=5.0:s2a=on:s2agt=16:i=41:si=on:rtra=on_0");
   quick.push("dis+10_1:128_ind=both:indmd=1:indstrhyp=on:nui=on:sac=on:i=45:si=on:rtra=on_0");
   quick.push("ott+1002_1:4_drc=off:fde=unused:fsd=on:fsdmm=3:gtg=exists_all:gtgl=3:ind=struct:indgen=on:indoct=on:newcnf=on:norm_ineq=on:sp=occurrence:taea=off:to=lpo:i=84:si=on:rtra=on_0");
   quick.push("dis+10_1:1_av=off:fsd=on:fsr=off:gtg=exists_all:ind=struct:indc=goal:indgen=on:ss=axioms:i=66:si=on:rtra=on_0");
   quick.push("ott+1011_1:1_ind=struct:indstrhyp=on:newcnf=on:nui=on:s2a=on:i=74:si=on:rtra=on_0");
   quick.push("ott+1011_31:15_abs=on:drc=off:ev=cautious:gtg=position:gtgl=3:ind=struct:indc=goal:indmd=1:taea=off:to=lpo:i=179:si=on:rtra=on_0");
   quick.push("ott+1002_3:2_aac=none:abs=on:alpa=true:drc=off:gve=force:ind=struct:indao=on:newcnf=on:nicw=on:nm=30:rawr=on:taea=off:i=1038:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bce=on:drc=off:fsd=on:ind=struct:indgen=on:indgenss=2:sac=on:taea=off:to=lpo:uwa=interpreted_only:i=1022:si=on:rtra=on_0");
   quick.push("dis+10_1:1_av=off:bsd=on:fd=off:fnrw=on:gtg=all:gtgl=2:ind=both:indao=on:indc=goal:indgen=on:newcnf=on:plsq=on:plsqr=32,1:ss=axioms:i=89:si=on:rtra=on_0");
   quick.push("ott+1011_1:1_aac=none:fd=preordered:ind=struct:indao=on:newcnf=on:nm=0:nui=on:sik=three:sp=const_frequency:spb=intro:to=lpo:i=35:si=on:rtra=on_0");
   quick.push("ott+21_1:1_canc=cautious:cond=fast:drc=off:fd=preordered:ind=struct:indao=on:indgen=on:indgenss=1:indoct=on:newcnf=on:sik=recursion:sp=occurrence:taea=off:i=688:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_av=off:br=off:drc=off:gtg=exists_all:ind=both:indc=goal:indmd=15:plsq=on:plsqr=9,1:sos=on:sp=unary_frequency:tgt=ground:to=lpo:uace=off:uwa=one_side_interpreted:i=3:si=on:rtra=on_0");
   quick.push("ott+10_5:1_drc=off:ind=struct:indstrhyp=on:kws=precedence:taea=off:uwa=all:i=51:si=on:rtra=on_0");
   quick.push("dis+10_1:64_ind=both:indao=on:indstrhyp=on:intindint=infinite:newcnf=on:nm=0:ss=axioms:i=55:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_asg=cautious:gtg=all:ind=struct:indc=goal:norm_ineq=on:nui=on:s2a=on:i=111:si=on:rtra=on_0");
   quick.push("lrs+1011_1:7_drc=off:fsr=off:ind=struct:norm_ineq=on:s2a=on:taea=off:to=lpo:uace=off:uwa=interpreted_only:i=60:si=on:rtra=on_0");
   quick.push("dis+10_1:1024_av=off:ind=struct:indgen=on:indgenss=2:indmd=1:indstrhyp=on:sp=const_min:taea=off:to=lpo:i=38:si=on:rtra=on_0");
   quick.push("lrs+1010_1:128_aac=none:alpa=false:cond=fast:drc=off:gtg=position:gve=cautious:ind=both:norm_ineq=on:nwc=10.0:sac=on:sp=frequency:tgt=full:to=lpo:i=111:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_bd=preordered:gtg=exists_all:gtgl=3:ind=struct:indmd=1:indstrhyp=on:nui=on:sos=on:i=52:si=on:rtra=on_0");
  // Improves by expected 106.95111512053347 probs costing 3982 Mi
  // Sub-schedule for 8000Mi strat cap / 8000Mi overall limit
   quick.push("ott+10_1:12_bsd=on:drc=off:fde=none:ind=struct:indgen=on:indgenss=2:norm_ineq=on:sac=on:taea=off:thi=strong:uwa=ground:i=717:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bsd=on:drc=off:fd=preordered:ind=struct:indao=on:indgenss=7:kws=inv_arity:rawr=on:sac=on:sp=const_max:spb=intro:sup=off:uhcvi=on:updr=off:uwa=ground:i=1598:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_drc=off:ind=both:indoct=on:indstrhyp=on:sos=on:sp=const_frequency:ss=axioms:to=lpo:i=311:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bce=on:drc=off:fsd=on:ind=struct:indgen=on:indgenss=2:sac=on:taea=off:to=lpo:uwa=interpreted_only:i=1235:si=on:rtra=on_0");
   quick.push("ott+10_1:172_awrs=decay:drc=off:gtg=position:ind=both:indao=on:indc=goal:indgen=on:newcnf=on:sik=recursion:sp=weighted_frequency:taea=off:uhcvi=on:i=2892:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_drc=off:gtg=all:ind=both:indgen=on:indoct=on:sp=reverse_frequency:ss=axioms:to=lpo:i=102:si=on:rtra=on_0");
   quick.push("dis+21_1:1_ind=struct:indstrhyp=on:norm_ineq=on:rawr=on:s2a=on:spb=goal:to=lpo:uace=off:urr=on:i=34:si=on:rtra=on_0");
   quick.push("dis+1002_1:1024_av=off:bd=off:drc=off:fsr=off:gtg=position:ind=struct:indc=goal:indgen=on:indgenss=2:taea=off:to=lpo:i=1117:si=on:rtra=on_0");
  // Improves by expected 143.8120963705851 probs costing 7998 Mi
  // Sub-schedule for 20000Mi strat cap / 20000Mi overall limit
   quick.push("ott+2_1:1_av=off:ev=cautious:fd=preordered:ind=struct:indstrhyp=on:sos=on:i=198:si=on:rtra=on_0");
   quick.push("lrs+10_1:20_aac=none:asg=cautious:awrs=decay:bsd=on:drc=off:ev=force:flr=on:ind=both:indgen=on:indoct=on:nm=10:pum=on:sac=on:spb=units:taea=off:tgt=full:thi=neg_eq:to=lpo:i=368:si=on:rtra=on_0");
   quick.push("dis+1002_3:1_awrs=converge:awrsf=500:fsd=on:fsr=off:gve=cautious:nm=32:sos=on:sp=frequency:tgt=ground:to=lpo:uace=off:i=114:si=on:rtra=on_0");
   quick.push("dis+10_1:1_aac=none:alpa=true:drc=off:ind=both:indoct=on:newcnf=on:sac=on:taea=off:to=lpo:i=1035:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_drc=off:er=filter:fsr=off:ind=both:indao=on:newcnf=on:nm=32:rp=on:sac=on:sik=recursion:sp=unary_frequency:tac=rule:taea=off:to=lpo:uace=off:i=150:si=on:rtra=on_0");
   quick.push("ott+11_5:1_av=off:br=off:canc=cautious:drc=off:ev=cautious:fsr=off:ind=struct:indstrhyp=on:newcnf=on:i=530:si=on:rtra=on_0");
   quick.push("ott+10_1:12_bsd=on:drc=off:fde=none:ind=struct:indgen=on:indgenss=2:norm_ineq=on:sac=on:taea=off:thi=strong:uwa=ground:i=1648:si=on:rtra=on_0");
   quick.push("ott+1002_1:4_drc=off:fde=unused:fsd=on:fsdmm=3:gtg=exists_all:gtgl=3:ind=struct:indgen=on:indoct=on:newcnf=on:norm_ineq=on:sp=occurrence:taea=off:to=lpo:i=84:si=on:rtra=on_0");
   quick.push("ott+1011_1:1_ind=struct:indstrhyp=on:newcnf=on:nui=on:s2a=on:i=117:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_bsr=unit_only:ev=cautious:ind=both:nui=on:sac=on:i=446:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bce=on:drc=off:fsd=on:ind=struct:indgen=on:indgenss=2:sac=on:taea=off:to=lpo:uwa=interpreted_only:i=2262:si=on:rtra=on_0");
   quick.push("ott+1011_1:1_aac=none:fd=preordered:ind=struct:indao=on:newcnf=on:nm=0:nui=on:sik=three:sp=const_frequency:spb=intro:to=lpo:i=248:si=on:rtra=on_0");
   quick.push("ott+21_1:1_canc=cautious:cond=fast:drc=off:fd=preordered:ind=struct:indao=on:indgen=on:indgenss=1:indoct=on:newcnf=on:sik=recursion:sp=occurrence:taea=off:i=2535:si=on:rtra=on_0");
   quick.push("ott+10_1:172_awrs=decay:drc=off:gtg=position:ind=both:indao=on:indc=goal:indgen=on:newcnf=on:sik=recursion:sp=weighted_frequency:taea=off:uhcvi=on:i=8568:si=on:rtra=on_0");
   quick.push("lrs+10_1:128_drc=off:gtg=exists_top:ind=struct:indstrhyp=on:sac=on:slsq=on:slsqc=1:taea=off:i=61:si=on:rtra=on_0");
   quick.push("lrs+10_8:1_gtg=all:ind=struct:indmd=2:indoct=on:kws=frequency:lma=on:nui=on:sos=on:sp=reverse_frequency:taea=off:i=172:si=on:rtra=on_0");
   quick.push("ott+21_1:10_bsr=on:canc=force:drc=encompass:ev=cautious:ile=on:ind=struct:indao=on:indoct=on:newcnf=on:spb=non_intro:tac=rule:taea=off:to=lpo:i=849:si=on:rtra=on_0");
   quick.push("dis+21_1:1_ind=struct:indstrhyp=on:norm_ineq=on:rawr=on:s2a=on:spb=goal:to=lpo:uace=off:urr=on:i=38:si=on:rtra=on_0");
   quick.push("lrs+1011_1:7_drc=off:fsr=off:ind=struct:norm_ineq=on:s2a=on:taea=off:to=lpo:uace=off:uwa=interpreted_only:i=60:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_bd=preordered:gtg=exists_all:gtgl=3:ind=struct:indmd=1:indstrhyp=on:nui=on:sos=on:i=411:si=on:rtra=on_0");
   quick.push("lrs+1011_1:16_drc=off:gtg=position:kws=precedence:sd=1:sp=unary_first:ss=axioms:st=2.0:i=112:si=on:rtra=on_0");
  // Improves by expected 153.73430619163955 probs costing 19985 Mi
  // Sub-schedule for 40000Mi strat cap / 40000Mi overall limit
   quick.push("ott+10_1:1_aac=none:alpa=true:drc=encompass:fsr=off:ind=both:indoct=on:taea=off:i=1673:si=on:rtra=on_0");
   quick.push("lrs+10_1:20_aac=none:asg=cautious:awrs=decay:bsd=on:drc=off:ev=force:flr=on:ind=both:indgen=on:indoct=on:nm=10:pum=on:sac=on:spb=units:taea=off:tgt=full:thi=neg_eq:to=lpo:i=6328:si=on:rtra=on_0");
   quick.push("dis+1002_3:1_awrs=converge:awrsf=500:fsd=on:fsr=off:gve=cautious:nm=32:sos=on:sp=frequency:tgt=ground:to=lpo:uace=off:i=114:si=on:rtra=on_0");
   quick.push("dis+1010_5:1_gtg=position:kws=inv_arity:sas=z3:sp=reverse_arity:tgt=full:urr=on:i=273:si=on:rtra=on_0");
   quick.push("lrs+1010_1:3_drc=encompass:ind=both:indmd=1:nui=on:s2a=on:ss=axioms:i=67:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_drc=off:er=filter:fsr=off:ind=both:indao=on:newcnf=on:nm=32:rp=on:sac=on:sik=recursion:sp=unary_frequency:tac=rule:taea=off:to=lpo:uace=off:i=535:si=on:rtra=on_0");
   quick.push("dis+10_1:128_ind=both:indmd=1:indstrhyp=on:nui=on:sac=on:i=1116:si=on:rtra=on_0");
   quick.push("ott+10_1:12_bsd=on:drc=off:fde=none:ind=struct:indgen=on:indgenss=2:norm_ineq=on:sac=on:taea=off:thi=strong:uwa=ground:i=7065:si=on:rtra=on_0");
   quick.push("ott+1002_1:4_drc=off:fde=unused:fsd=on:fsdmm=3:gtg=exists_all:gtgl=3:ind=struct:indgen=on:indoct=on:newcnf=on:norm_ineq=on:sp=occurrence:taea=off:to=lpo:i=84:si=on:rtra=on_0");
   quick.push("ott+1011_1:1_aac=none:drc=encompass:er=filter:erml=2:gtg=exists_all:gve=cautious:ind=both:indmd=1:newcnf=on:nwc=2.0:sas=z3:sp=unary_first:to=lpo:i=753:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_atotf=0.2:drc=off:gtg=exists_top:ind=both:nwc=10.0:sac=on:sp=unary_frequency:tgt=ground:to=lpo:i=56:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bsd=on:drc=off:fd=preordered:ind=struct:indao=on:indgenss=7:kws=inv_arity:rawr=on:sac=on:sp=const_max:spb=intro:sup=off:uhcvi=on:updr=off:uwa=ground:i=3557:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_drc=off:ind=both:indoct=on:indstrhyp=on:sos=on:sp=const_frequency:ss=axioms:to=lpo:i=1160:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bce=on:drc=off:fsd=on:ind=struct:indgen=on:indgenss=2:sac=on:taea=off:to=lpo:uwa=interpreted_only:i=5614:si=on:rtra=on_0");
   quick.push("ott+10_1:128_awrs=converge:awrsf=500:bsr=on:drc=off:er=known:ev=force:fde=none:gsp=on:ind=struct:indgen=on:indgenss=2:indstrhyp=on:irw=on:sac=on:sos=theory:taea=off:tgt=full:to=lpo:uwa=one_side_interpreted:i=549:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_avsq=on:avsqc=1:avsqr=1,16:drc=off:ev=force:ind=struct:sos=on:to=lpo:urr=on:i=197:si=on:rtra=on_0");
   quick.push("ott+21_1:1_canc=cautious:cond=fast:drc=off:fd=preordered:ind=struct:indao=on:indgen=on:indgenss=1:indoct=on:newcnf=on:sik=recursion:sp=occurrence:taea=off:i=10416:si=on:rtra=on_0");
   quick.push("lrs+1010_5:1_asg=cautious:av=off:fsd=on:gtg=exists_sym:ind=both:indgen=on:indgenss=4:kws=precedence:lwlo=on:nm=30:sos=theory:sp=const_frequency:taea=off:tar=off:i=158:si=on:rtra=on_0");
   quick.push("ott+1011_1:64_avsq=on:avsqr=11223,262144:drc=off:ev=force:lsd=10:nm=16:plsq=on:plsqc=1:plsqr=1,32:rawr=on:sp=unary_frequency:spb=goal:taea=off:tgt=ground:to=lpo:i=240:si=on:rtra=on_0");
  // Improves by expected 115.18506679466628 probs costing 39936 Mi
  // Sub-schedule for 120000Mi strat cap / 120000Mi overall limit
   quick.push("ott+10_1:1_drc=encompass:foolp=on:ind=struct:indoct=on:sac=on:taea=off:to=lpo:i=1906:si=on:rtra=on_0");
   quick.push("ott+1011_2:1_av=off:ev=cautious:ind=both:indmd=10:indstrhyp=on:newcnf=on:nm=0:rawr=on:sp=unary_frequency:urr=on:i=486:si=on:rtra=on_0");
   quick.push("lrs+10_1:20_aac=none:asg=cautious:awrs=decay:bsd=on:drc=off:ev=force:flr=on:ind=both:indgen=on:indoct=on:nm=10:pum=on:sac=on:spb=units:taea=off:tgt=full:thi=neg_eq:to=lpo:i=982:si=on:rtra=on_0");
   quick.push("lrs+1010_1:3_drc=encompass:ind=both:indmd=1:nui=on:s2a=on:ss=axioms:i=67:si=on:rtra=on_0");
   quick.push("ott+10_1:12_bsd=on:drc=off:fde=none:ind=struct:indgen=on:indgenss=2:norm_ineq=on:sac=on:taea=off:thi=strong:uwa=ground:i=3679:si=on:rtra=on_0");
   quick.push("dis+10_33:64_aac=none:add=large:drc=off:gtg=exists_sym:ind=struct:indmd=4:indoct=on:indstrhyp=on:nm=0:pum=on:sac=on:sp=const_min:thi=all:i=1560:si=on:rtra=on_0");
   quick.push("ott+1002_3:2_aac=none:abs=on:alpa=true:drc=off:gve=force:ind=struct:indao=on:newcnf=on:nicw=on:nm=30:rawr=on:taea=off:i=11963:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bce=on:drc=off:fsd=on:ind=struct:indgen=on:indgenss=2:sac=on:taea=off:to=lpo:uwa=interpreted_only:i=5614:si=on:rtra=on_0");
   quick.push("ott+1011_1:1_aac=none:fd=preordered:ind=struct:indao=on:newcnf=on:nm=0:nui=on:sik=three:sp=const_frequency:spb=intro:to=lpo:i=248:si=on:rtra=on_0");
   quick.push("dis+10_21:29_bd=off:br=off:drc=off:ev=cautious:gs=on:gtg=exists_sym:ind=struct:indgen=on:indgenss=2:lcm=reverse:s2agt=10:sac=on:slsq=on:slsqc=2:sos=all:sp=const_frequency:taea=off:tgt=full:i=35938:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_avsq=on:avsqc=1:avsqr=1,16:drc=off:ev=force:ind=struct:sos=on:to=lpo:urr=on:i=197:si=on:rtra=on_0");
   quick.push("ott+21_1:1_canc=cautious:cond=fast:drc=off:fd=preordered:ind=struct:indao=on:indgen=on:indgenss=1:indoct=on:newcnf=on:sik=recursion:sp=occurrence:taea=off:i=17422:si=on:rtra=on_0");
   quick.push("ott+10_1:172_awrs=decay:drc=off:gtg=position:ind=both:indao=on:indc=goal:indgen=on:newcnf=on:sik=recursion:sp=weighted_frequency:taea=off:uhcvi=on:i=39081:si=on:rtra=on_0");
   quick.push("lrs+1010_5:1_asg=cautious:av=off:fsd=on:gtg=exists_sym:ind=both:indgen=on:indgenss=4:kws=precedence:lwlo=on:nm=30:sos=theory:sp=const_frequency:taea=off:tar=off:i=120:si=on:rtra=on_0");
   quick.push("ott+1011_1:64_avsq=on:avsqr=11223,262144:drc=off:ev=force:lsd=10:nm=16:plsq=on:plsqc=1:plsqr=1,32:rawr=on:sp=unary_frequency:spb=goal:taea=off:tgt=ground:to=lpo:i=191:si=on:rtra=on_0");
   quick.push("dis+21_1:1_ind=struct:indstrhyp=on:norm_ineq=on:rawr=on:s2a=on:spb=goal:to=lpo:uace=off:urr=on:i=156:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_bd=preordered:gtg=exists_all:gtgl=3:ind=struct:indmd=1:indstrhyp=on:nui=on:sos=on:i=369:si=on:rtra=on_0");
  // Improves by expected 136.55861875083716 probs costing 119962 Mi
  // Sub-schedule for 240000Mi strat cap / 240000Mi overall limit
   quick.push("ott+10_1:1_aac=none:alpa=true:drc=encompass:fsr=off:ind=both:indoct=on:taea=off:i=3405:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_abs=on:fnrw=on:fsr=off:gtg=exists_sym:gtgl=4:newcnf=on:nm=2:rp=on:sas=z3:sp=occurrence:thi=neg_eq:i=2238:si=on:rtra=on_0");
   quick.push("ott+10_1:1_drc=encompass:foolp=on:ind=struct:indoct=on:sac=on:taea=off:to=lpo:i=1183:si=on:rtra=on_0");
   quick.push("ott+1011_2:1_av=off:ev=cautious:ind=both:indmd=10:indstrhyp=on:newcnf=on:nm=0:rawr=on:sp=unary_frequency:urr=on:i=486:si=on:rtra=on_0");
   quick.push("lrs+10_1:20_aac=none:asg=cautious:awrs=decay:bsd=on:drc=off:ev=force:flr=on:ind=both:indgen=on:indoct=on:nm=10:pum=on:sac=on:spb=units:taea=off:tgt=full:thi=neg_eq:to=lpo:i=982:si=on:rtra=on_0");
   quick.push("dis+10_1:1_aac=none:alpa=true:drc=off:ind=both:indoct=on:newcnf=on:sac=on:taea=off:to=lpo:i=6648:si=on:rtra=on_0");
   quick.push("lrs+1010_1:3_drc=encompass:ind=both:indmd=1:nui=on:s2a=on:ss=axioms:i=67:si=on:rtra=on_0");
   quick.push("dis+10_1:128_ind=both:indmd=1:indstrhyp=on:nui=on:sac=on:i=1708:si=on:rtra=on_0");
   quick.push("ott+10_1:12_bsd=on:drc=off:fde=none:ind=struct:indgen=on:indgenss=2:norm_ineq=on:sac=on:taea=off:thi=strong:uwa=ground:i=23300:si=on:rtra=on_0");
   quick.push("ott+1011_1:1_aac=none:drc=encompass:er=filter:erml=2:gtg=exists_all:gve=cautious:ind=both:indmd=1:newcnf=on:nwc=2.0:sas=z3:sp=unary_first:to=lpo:i=1027:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bsd=on:drc=off:fd=preordered:ind=struct:indao=on:indgenss=7:kws=inv_arity:rawr=on:sac=on:sp=const_max:spb=intro:sup=off:uhcvi=on:updr=off:uwa=ground:i=18822:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_drc=off:ind=both:indoct=on:indstrhyp=on:sos=on:sp=const_frequency:ss=axioms:to=lpo:i=574:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bce=on:drc=off:fsd=on:ind=struct:indgen=on:indgenss=2:sac=on:taea=off:to=lpo:uwa=interpreted_only:i=8598:si=on:rtra=on_0");
   quick.push("dis+10_21:29_bd=off:br=off:drc=off:ev=cautious:gs=on:gtg=exists_sym:ind=struct:indgen=on:indgenss=2:lcm=reverse:s2agt=10:sac=on:slsq=on:slsqc=2:sos=all:sp=const_frequency:taea=off:tgt=full:i=115235:si=on:rtra=on_0");
   quick.push("ott+10_1:172_awrs=decay:drc=off:gtg=position:ind=both:indao=on:indc=goal:indgen=on:newcnf=on:sik=recursion:sp=weighted_frequency:taea=off:uhcvi=on:i=45312:si=on:rtra=on_0");
   quick.push("lrs+1010_5:1_asg=cautious:av=off:fsd=on:gtg=exists_sym:ind=both:indgen=on:indgenss=4:kws=precedence:lwlo=on:nm=30:sos=theory:sp=const_frequency:taea=off:tar=off:i=120:si=on:rtra=on_0");
   quick.push("lrs+10_8:1_gtg=all:ind=struct:indmd=2:indoct=on:kws=frequency:lma=on:nui=on:sos=on:sp=reverse_frequency:taea=off:i=1165:si=on:rtra=on_0");
   quick.push("ott+1011_1:64_avsq=on:avsqr=11223,262144:drc=off:ev=force:lsd=10:nm=16:plsq=on:plsqc=1:plsqr=1,32:rawr=on:sp=unary_frequency:spb=goal:taea=off:tgt=ground:to=lpo:i=421:si=on:rtra=on_0");
   quick.push("ott+21_1:10_bsr=on:canc=force:drc=encompass:ev=cautious:ile=on:ind=struct:indao=on:indoct=on:newcnf=on:spb=non_intro:tac=rule:taea=off:to=lpo:i=5032:si=on:rtra=on_0");
   quick.push("dis+1002_1:1024_av=off:bd=off:drc=off:fsr=off:gtg=position:ind=struct:indc=goal:indgen=on:indgenss=2:taea=off:to=lpo:i=2124:si=on:rtra=on_0");
   quick.push("lrs+1010_1:128_aac=none:alpa=false:cond=fast:drc=off:gtg=position:gve=cautious:ind=both:norm_ineq=on:nwc=10.0:sac=on:sp=frequency:tgt=full:to=lpo:i=561:si=on:rtra=on_0");
  // Improves by expected 79.18911371902213 probs costing 238987 Mi
  // Sub-schedule for 480000Mi strat cap / 480000Mi overall limit
   quick.push("ott+1011_2:1_av=off:ev=cautious:ind=both:indmd=10:indstrhyp=on:newcnf=on:nm=0:rawr=on:sp=unary_frequency:urr=on:i=4301:si=on:rtra=on_0");
   quick.push("lrs+10_1:20_aac=none:asg=cautious:awrs=decay:bsd=on:drc=off:ev=force:flr=on:ind=both:indgen=on:indoct=on:nm=10:pum=on:sac=on:spb=units:taea=off:tgt=full:thi=neg_eq:to=lpo:i=16506:si=on:rtra=on_0");
   quick.push("ott+10_1:12_bsd=on:drc=off:fde=none:ind=struct:indgen=on:indgenss=2:norm_ineq=on:sac=on:taea=off:thi=strong:uwa=ground:i=113485:si=on:rtra=on_0");
   quick.push("dis+10_33:64_aac=none:add=large:drc=off:gtg=exists_sym:ind=struct:indmd=4:indoct=on:indstrhyp=on:nm=0:pum=on:sac=on:sp=const_min:thi=all:i=18587:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_bsr=unit_only:ev=cautious:ind=both:nui=on:sac=on:i=3319:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bce=on:drc=off:fsd=on:ind=struct:indgen=on:indgenss=2:sac=on:taea=off:to=lpo:uwa=interpreted_only:i=26087:si=on:rtra=on_0");
   quick.push("dis+10_21:29_bd=off:br=off:drc=off:ev=cautious:gs=on:gtg=exists_sym:ind=struct:indgen=on:indgenss=2:lcm=reverse:s2agt=10:sac=on:slsq=on:slsqc=2:sos=all:sp=const_frequency:taea=off:tgt=full:i=84824:si=on:rtra=on_0");
   quick.push("ott+2_1:1_drc=off:fs=off:fsr=off:ind=both:indgen=on:indgenss=2:indoct=on:sac=on:sp=occurrence:i=13173:si=on:rtra=on_0");
   quick.push("ott+21_1:1_canc=cautious:cond=fast:drc=off:fd=preordered:ind=struct:indao=on:indgen=on:indgenss=1:indoct=on:newcnf=on:sik=recursion:sp=occurrence:taea=off:i=56164:si=on:rtra=on_0");
   quick.push("ott+10_1:172_awrs=decay:drc=off:gtg=position:ind=both:indao=on:indc=goal:indgen=on:newcnf=on:sik=recursion:sp=weighted_frequency:taea=off:uhcvi=on:i=142751:si=on:rtra=on_0");
   quick.push("lrs+1010_5:1_asg=cautious:av=off:fsd=on:gtg=exists_sym:ind=both:indgen=on:indgenss=4:kws=precedence:lwlo=on:nm=30:sos=theory:sp=const_frequency:taea=off:tar=off:i=158:si=on:rtra=on_0");
  // Improves by expected 57.473513520147854 probs costing 479344 Mi
  // Sub-schedule for 960000Mi strat cap / 960000Mi overall limit
   quick.push("ott+10_1:1_aac=none:alpa=true:drc=encompass:fsr=off:ind=both:indoct=on:taea=off:i=17958:si=on:rtra=on_0");
   quick.push("dis+10_1:1_anc=none:gtg=exists_sym:gtgl=5:ind=struct:indgen=on:indoct=on:s2a=on:sac=on:ss=axioms:i=137973:si=on:rtra=on_0");
   quick.push("ott+10_1:1_drc=encompass:foolp=on:ind=struct:indoct=on:sac=on:taea=off:to=lpo:i=25643:si=on:rtra=on_0");
   quick.push("lrs+10_1:20_aac=none:asg=cautious:awrs=decay:bsd=on:drc=off:ev=force:flr=on:ind=both:indgen=on:indoct=on:nm=10:pum=on:sac=on:spb=units:taea=off:tgt=full:thi=neg_eq:to=lpo:i=38951:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_drc=off:er=filter:fsr=off:ind=both:indao=on:newcnf=on:nm=32:rp=on:sac=on:sik=recursion:sp=unary_frequency:tac=rule:taea=off:to=lpo:uace=off:i=22096:si=on:rtra=on_0");
   quick.push("ott+10_1:12_bsd=on:drc=off:fde=none:ind=struct:indgen=on:indgenss=2:norm_ineq=on:sac=on:taea=off:thi=strong:uwa=ground:i=140433:si=on:rtra=on_0");
   quick.push("dis+10_33:64_aac=none:add=large:drc=off:gtg=exists_sym:ind=struct:indmd=4:indoct=on:indstrhyp=on:nm=0:pum=on:sac=on:sp=const_min:thi=all:i=50959:si=on:rtra=on_0");
   quick.push("ott+1002_3:2_aac=none:abs=on:alpa=true:drc=off:gve=force:ind=struct:indao=on:newcnf=on:nicw=on:nm=30:rawr=on:taea=off:i=79001:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bsd=on:drc=off:fd=preordered:ind=struct:indao=on:indgenss=7:kws=inv_arity:rawr=on:sac=on:sp=const_max:spb=intro:sup=off:uhcvi=on:updr=off:uwa=ground:i=45001:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bce=on:drc=off:fsd=on:ind=struct:indgen=on:indgenss=2:sac=on:taea=off:to=lpo:uwa=interpreted_only:i=49784:si=on:rtra=on_0");
   quick.push("dis+10_21:29_bd=off:br=off:drc=off:ev=cautious:gs=on:gtg=exists_sym:ind=struct:indgen=on:indgenss=2:lcm=reverse:s2agt=10:sac=on:slsq=on:slsqc=2:sos=all:sp=const_frequency:taea=off:tgt=full:i=140001:si=on:rtra=on_0");
   quick.push("ott+21_1:1_canc=cautious:cond=fast:drc=off:fd=preordered:ind=struct:indao=on:indgen=on:indgenss=1:indoct=on:newcnf=on:sik=recursion:sp=occurrence:taea=off:i=71989:si=on:rtra=on_0");
   quick.push("ott+10_1:172_awrs=decay:drc=off:gtg=position:ind=both:indao=on:indc=goal:indgen=on:newcnf=on:sik=recursion:sp=weighted_frequency:taea=off:uhcvi=on:i=124992:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_drc=encompass:ind=struct:indao=on:newcnf=on:plsq=on:plsqr=32,1:sp=frequency:to=lpo:i=3032:si=on:rtra=on_0");
   quick.push("ott+21_1:10_bsr=on:canc=force:drc=encompass:ev=cautious:ile=on:ind=struct:indao=on:indoct=on:newcnf=on:spb=non_intro:tac=rule:taea=off:to=lpo:i=11986:si=on:rtra=on_0");
  // Improves by expected 35.58186707682759 probs costing 959784 Mi
  // Sub-schedule for 960000Mi strat cap / 960000Mi overall limit
   quick.push("dis+10_1:1_anc=none:gtg=exists_sym:gtgl=5:ind=struct:indgen=on:indoct=on:s2a=on:sac=on:ss=axioms:i=133107:si=on:rtra=on_0");
   quick.push("ott+10_1:1_drc=encompass:foolp=on:ind=struct:indoct=on:sac=on:taea=off:to=lpo:i=21939:si=on:rtra=on_0");
   quick.push("lrs+10_1:20_aac=none:asg=cautious:awrs=decay:bsd=on:drc=off:ev=force:flr=on:ind=both:indgen=on:indoct=on:nm=10:pum=on:sac=on:spb=units:taea=off:tgt=full:thi=neg_eq:to=lpo:i=126079:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_drc=off:er=filter:fsr=off:ind=both:indao=on:newcnf=on:nm=32:rp=on:sac=on:sik=recursion:sp=unary_frequency:tac=rule:taea=off:to=lpo:uace=off:i=63511:si=on:rtra=on_0");
   quick.push("ott+10_1:12_bsd=on:drc=off:fde=none:ind=struct:indgen=on:indgenss=2:norm_ineq=on:sac=on:taea=off:thi=strong:uwa=ground:i=91551:si=on:rtra=on_0");
   quick.push("dis+10_33:64_aac=none:add=large:drc=off:gtg=exists_sym:ind=struct:indmd=4:indoct=on:indstrhyp=on:nm=0:pum=on:sac=on:sp=const_min:thi=all:i=43010:si=on:rtra=on_0");
   quick.push("ott+1002_3:2_aac=none:abs=on:alpa=true:drc=off:gve=force:ind=struct:indao=on:newcnf=on:nicw=on:nm=30:rawr=on:taea=off:i=20149:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bsd=on:drc=off:fd=preordered:ind=struct:indao=on:indgenss=7:kws=inv_arity:rawr=on:sac=on:sp=const_max:spb=intro:sup=off:uhcvi=on:updr=off:uwa=ground:i=34870:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bce=on:drc=off:fsd=on:ind=struct:indgen=on:indgenss=2:sac=on:taea=off:to=lpo:uwa=interpreted_only:i=124459:si=on:rtra=on_0");
   quick.push("dis+10_21:29_bd=off:br=off:drc=off:ev=cautious:gs=on:gtg=exists_sym:ind=struct:indgen=on:indgenss=2:lcm=reverse:s2agt=10:sac=on:slsq=on:slsqc=2:sos=all:sp=const_frequency:taea=off:tgt=full:i=123527:si=on:rtra=on_0");
   quick.push("ott+21_1:1_canc=cautious:cond=fast:drc=off:fd=preordered:ind=struct:indao=on:indgen=on:indgenss=1:indoct=on:newcnf=on:sik=recursion:sp=occurrence:taea=off:i=39284:si=on:rtra=on_0");
   quick.push("ott+10_1:172_awrs=decay:drc=off:gtg=position:ind=both:indao=on:indc=goal:indgen=on:newcnf=on:sik=recursion:sp=weighted_frequency:taea=off:uhcvi=on:i=124992:si=on:rtra=on_0");
  // Improves by expected 13.948651891536842 probs costing 946466 Mi
  // Sub-schedule for 960000Mi strat cap / 960000Mi overall limit
   quick.push("dis+10_1:1_anc=none:gtg=exists_sym:gtgl=5:ind=struct:indgen=on:indoct=on:s2a=on:sac=on:ss=axioms:i=120877:si=on:rtra=on_0");
   quick.push("ott+10_1:1_drc=encompass:foolp=on:ind=struct:indoct=on:sac=on:taea=off:to=lpo:i=21939:si=on:rtra=on_0");
   quick.push("lrs+10_1:20_aac=none:asg=cautious:awrs=decay:bsd=on:drc=off:ev=force:flr=on:ind=both:indgen=on:indoct=on:nm=10:pum=on:sac=on:spb=units:taea=off:tgt=full:thi=neg_eq:to=lpo:i=16287:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_drc=off:er=filter:fsr=off:ind=both:indao=on:newcnf=on:nm=32:rp=on:sac=on:sik=recursion:sp=unary_frequency:tac=rule:taea=off:to=lpo:uace=off:i=63511:si=on:rtra=on_0");
   quick.push("ott+10_1:12_bsd=on:drc=off:fde=none:ind=struct:indgen=on:indgenss=2:norm_ineq=on:sac=on:taea=off:thi=strong:uwa=ground:i=113322:si=on:rtra=on_0");
   quick.push("dis+10_33:64_aac=none:add=large:drc=off:gtg=exists_sym:ind=struct:indmd=4:indoct=on:indstrhyp=on:nm=0:pum=on:sac=on:sp=const_min:thi=all:i=69001:si=on:rtra=on_0");
   quick.push("ott+1002_3:2_aac=none:abs=on:alpa=true:drc=off:gve=force:ind=struct:indao=on:newcnf=on:nicw=on:nm=30:rawr=on:taea=off:i=75001:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bsd=on:drc=off:fd=preordered:ind=struct:indao=on:indgenss=7:kws=inv_arity:rawr=on:sac=on:sp=const_max:spb=intro:sup=off:uhcvi=on:updr=off:uwa=ground:i=34870:si=on:rtra=on_0");
   quick.push("dis+1011_8:1_abs=on:bd=off:canc=cautious:ev=force:ind=int:indc=goal_plus:kws=inv_frequency:s2a=on:s2agt=10:sas=z3:sp=reverse_arity:ss=included:tgt=ground:i=33001:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bce=on:drc=off:fsd=on:ind=struct:indgen=on:indgenss=2:sac=on:taea=off:to=lpo:uwa=interpreted_only:i=122070:si=on:rtra=on_0");
   quick.push("dis+10_21:29_bd=off:br=off:drc=off:ev=cautious:gs=on:gtg=exists_sym:ind=struct:indgen=on:indgenss=2:lcm=reverse:s2agt=10:sac=on:slsq=on:slsqc=2:sos=all:sp=const_frequency:taea=off:tgt=full:i=123336:si=on:rtra=on_0");
   quick.push("ott+21_1:1_canc=cautious:cond=fast:drc=off:fd=preordered:ind=struct:indao=on:indgen=on:indgenss=1:indoct=on:newcnf=on:sik=recursion:sp=occurrence:taea=off:i=39735:si=on:rtra=on_0");
   quick.push("ott+10_1:172_awrs=decay:drc=off:gtg=position:ind=both:indao=on:indc=goal:indgen=on:newcnf=on:sik=recursion:sp=weighted_frequency:taea=off:uhcvi=on:i=124992:si=on:rtra=on_0");
  // Improves by expected 7.613387054318119 probs costing 957929 Mi
  // Overall score 6682.615103801281 probs on average / budget 3780367 Mi
}

void Schedules::getStructInductionTipSchedule(const Shell::Property& property, Schedule& quick, Schedule& fallback) {
  // Ran on tipvampire231219_nolemmas.txt
  // Sub-schedule for 2000Mi strat cap / 2000Mi overall limit
   quick.push("lrs+10_1:1024_fnrw=on:gtg=all:gtgl=3:ind=struct:indao=on:indc=goal:indoct=on:newcnf=on:sac=on:sp=unary_first:i=43:si=on:rtra=on_0");
   quick.push("lrs+21_1:128_gtg=exists_top:gtgl=2:ind=both:indc=goal_plus:indmd=1:newcnf=on:nm=20:nui=on:sik=recursion:sp=unary_frequency:spb=non_intro:i=19:si=on:rtra=on_0");
   quick.push("lrs+10_1:40_bsr=unit_only:drc=off:flr=on:ind=both:newcnf=on:nm=75:nui=on:sik=recursion:sp=const_min:updr=off:i=28:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_aac=none:gtg=exists_all:gtgl=3:ind=both:newcnf=on:nui=on:plsq=on:plsqr=4,1:rp=on:sik=recursion:spb=goal_then_units:i=22:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_drc=off:er=filter:fsr=off:ind=both:indao=on:newcnf=on:nm=32:rp=on:sac=on:sik=recursion:sp=unary_frequency:tac=rule:taea=off:to=lpo:uace=off:i=8:si=on:rtra=on_0");
   quick.push("dis+10_1:1_flr=on:ind=both:kws=precedence:newcnf=on:nui=on:sik=recursion:i=25:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_tac=light:taea=off:i=32:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_av=off:drc=off:ind=struct:indstrhyp=on:newcnf=on:sik=all:taea=off:urr=on:i=74:si=on:rtra=on_0");
   quick.push("lrs+1010_1:128_add=large:bs=on:bsd=on:etr=on:ev=force:fnrw=on:ind=struct:indc=goal_plus:indmd=2:indoct=on:lecc=2.0:newcnf=on:nui=on:sp=unary_first:i=89:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_avsq=on:avsql=on:drc=off:ind=struct:indmd=20:kws=precedence:newcnf=on:rp=on:sas=z3:sp=const_max:i=260:si=on:rtra=on_0");
   quick.push("dis+10_1:1_bs=unit_only:fde=unused:fnrw=on:ind=int:indn=off:ins=1:intindstcomp=always:kws=arity:newcnf=on:rp=on:sp=frequency:tac=rule:taea=off:tgt=full:urr=on:i=28:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_ind=struct:newcnf=on:nui=on:nwc=10.0:sac=on:sik=recursion:to=lpo:i=16:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_fnrw=on:ind=both:indmd=2:indoct=on:kws=frequency:newcnf=on:nui=on:sik=recursion:taea=off:i=13:si=on:rtra=on_0");
   quick.push("ott+10_1:1_ind=struct:indstrhyp=on:kws=precedence:s2a=on:s2agt=16:sac=on:sos=all:sp=reverse_arity:spb=intro:i=71:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_drc=encompass:ind=struct:indao=on:newcnf=on:plsq=on:plsqr=32,1:sp=frequency:to=lpo:i=8:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_aac=none:afp=10000:fnrw=on:ind=both:indc=goal_plus:indmd=1:indn=off:newcnf=on:i=4:si=on:rtra=on_0");
   quick.push("dis+10_1:1_asg=cautious:ind=both:intindstterm=no_skolems:newcnf=on:norm_ineq=on:rp=on:sac=on:sas=z3:sos=theory:spb=intro:to=lpo:i=174:si=on:rtra=on_0");
   quick.push("lrs+10_1633:262144_canc=cautious:drc=off:ev=force:fde=none:ind=both:indoct=on:newcnf=on:sik=recursion:sil=100000:sp=const_min:spb=goal_then_units:to=lpo:updr=off:i=15:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_bd=off:gtg=exists_all:ind=both:indmd=1:indstrhyp=on:ins=3:newcnf=on:nui=on:spb=goal_then_units:to=lpo:i=19:si=on:rtra=on_0");
   quick.push("ott+10_1:1_drc=off:fs=off:fsr=off:ind=struct:indstrhyp=on:nwc=5.0:s2a=on:sos=on:tar=off:i=60:si=on:rtra=on_0");
   quick.push("lrs-1003_1:4_av=off:drc=off:ind=struct:indu=off:kws=precedence:newcnf=on:rawr=on:s2a=on:s2agt=16:sil=100000:slsq=on:spb=units:urr=on:uwa=ground:i=31:si=on:rtra=on_0");
   quick.push("ott+10_1:1_drc=encompass:gtg=exists_all:ind=struct:indmd=3:indstrhyp=on:s2a=on:i=27:si=on:rtra=on_0");
   quick.push("dis+1010_3:1_aac=none:flr=on:ind=struct:ins=2:newcnf=on:nwc=2.0:sac=on:sil=100000:i=69:si=on:rtra=on_0");
   quick.push("lrs+2_1:4_drc=off:gtg=position:gve=cautious:ile=on:ind=struct:indao=on:indc=goal:indmd=6:newcnf=on:nwc=5.0:s2a=on:tac=axiom:to=lpo:i=39:si=on:rtra=on_0");
   quick.push("lrs+1002_1:8_alpa=false:bd=preordered:drc=off:ind=struct:newcnf=on:nwc=10.0:sac=on:sik=recursion:sp=occurrence:spb=goal:i=10:si=on:rtra=on_0");
   quick.push("ott+10_1:1_drc=off:fnrw=on:gtg=all:gtgl=3:ind=both:indao=on:kws=precedence:newcnf=on:nwc=6.0:sac=on:sp=reverse_arity:uwa=interpreted_only:i=11:si=on:rtra=on_0");
   quick.push("ott+10_1:1_add=large:flr=on:ind=both:newcnf=on:nui=on:nwc=5.0:sik=all:sil=100000:spb=non_intro:i=13:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_av=off:bd=off:gtg=exists_top:ind=struct:indao=on:kws=precedence:newcnf=on:nwc=10.0:sik=recursion:sil=100000:sp=frequency:taea=off:uwa=all:i=16:si=on:rtra=on_0");
   quick.push("ott+10_1:1_ev=cautious:gtg=exists_top:ind=struct:indc=goal:indstrhyp=on:nwc=10.0:sos=on:i=7:si=on:rtra=on_0");
   quick.push("ott+21_1:1_ep=RST:fsd=on:gve=cautious:ind=both:indn=off:newcnf=on:nui=on:nwc=10.0:sik=recursion:spb=intro:urr=on:i=4:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_gtg=exists_all:ind=both:indmd=1:newcnf=on:nui=on:taea=off:updr=off:i=18:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_drc=encompass:erd=off:ind=struct:indmd=1:sos=on:ss=axioms:urr=on:i=21:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_add=large:drc=encompass:gtg=exists_sym:ind=both:indmd=2:newcnf=on:sik=recursion:sil=100000:uwa=one_side_constant:i=65:si=on:rtra=on_0");
   quick.push("lrs+21_1:8_av=off:awrs=converge:awrsf=10:drc=off:fnrw=on:ind=struct:newcnf=on:slsq=on:slsqc=5:sp=unary_frequency:uwa=all:i=10:si=on:rtra=on_0");
   quick.push("ott+1002_1:1024_bsd=on:drc=off:fd=preordered:ind=struct:indao=on:indgenss=7:kws=inv_arity:rawr=on:sac=on:sp=const_max:spb=intro:sup=off:uhcvi=on:updr=off:uwa=ground:i=51:si=on:rtra=on_0");
   quick.push("ott+1002_3:2_aac=none:abs=on:alpa=true:drc=off:gve=force:ind=struct:indao=on:newcnf=on:nicw=on:nm=30:rawr=on:taea=off:i=8:si=on:rtra=on_0");
   quick.push("lrs+1002_1:4_drc=off:fsd=on:ind=struct:indmd=1:newcnf=on:nm=10:rp=on:s2pl=no:sik=recursion:sil=100000:sos=theory:sp=const_frequency:taea=off:uace=off:i=8:si=on:rtra=on_0");
   quick.push("dis+21_1:1_alpa=true:amm=off:fnrw=on:gtg=exists_top:gtgl=2:ind=struct:indc=goal:newcnf=on:rp=on:sil=100000:sos=theory:sp=frequency:taea=off:tgt=full:urr=on:i=82:si=on:rtra=on_0");
   quick.push("dis-1011_1:1_erd=off:gtg=exists_sym:gve=cautious:ind=both:indmd=3:indstrhyp=on:kws=inv_frequency:norm_ineq=on:sil=100000:sp=occurrence:spb=intro:ss=axioms:i=97:si=on:rtra=on_0");
   quick.push("ott+10_1:1_ind=both:newcnf=on:nui=on:plsq=on:sik=recursion:sp=unary_frequency:uwa=interpreted_only:i=2:si=on:rtra=on_0");
   quick.push("dis+10_1:1_av=off:fnrw=on:ind=struct:newcnf=on:nwc=5.0:i=9:si=on:rtra=on_0");
   quick.push("ott+10_1:1_atotf=0.1:ind=struct:indstrhyp=on:newcnf=on:sik=all:taea=off:i=177:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_bd=off:ep=RSTC:gtg=exists_all:newcnf=on:nm=10:norm_ineq=on:rp=on:s2agt=32:sac=on:sas=z3:slsq=on:slsqr=151023,1048576:sp=const_max:tac=light:i=161:si=on:rtra=on_0");
   quick.push("lrs+21_1:128_av=off:drc=encompass:gtg=all:ind=struct:indao=on:ins=1:newcnf=on:spb=units:uwa=one_side_interpreted:i=12:si=on:rtra=on_0");
   quick.push("lrs+1010_8:1_ind=both:indmd=2:kws=inv_precedence:newcnf=on:sik=recursion:sp=const_min:i=32:si=on:rtra=on_0");
   quick.push("dis+10_1:64_ind=both:indmd=2:indoct=on:newcnf=on:sac=on:sik=recursion:sil=100000:sp=frequency:taea=off:to=lpo:i=13:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_erd=off:gve=cautious:ind=both:newcnf=on:nui=on:updr=off:i=3:si=on:rtra=on_0");
   quick.push("lrs+10_1:4_drc=encompass:erd=off:ind=both:sil=100000:taea=off:urr=on:i=34:si=on:rtra=on_0");
  // Improves by expected 216.06498927478503 probs costing 1990 Mi
  // Sub-schedule for 4000Mi strat cap / 4000Mi overall limit
   quick.push("dis+10_180:31_canc=force:gtg=exists_all:gtgl=4:newcnf=on:rp=on:s2a=on:s2agt=10:sac=on:sas=z3:sos=all:uhcvi=on:i=223:si=on:rtra=on_0");
   quick.push("ott+21_1:5_drc=off:erd=off:ind=both:indgen=on:indgenss=5:sac=on:slsq=on:taea=off:urr=on:i=391:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_fnrw=on:gtg=exists_sym:gtgl=4:newcnf=on:rp=on:sil=100000:sp=frequency:taea=off:tgt=full:to=lpo:i=51:si=on:rtra=on_0");
   quick.push("lrs+1002_1:6_canc=cautious:cond=on:ind=both:indao=on:intindint=infinite:intindsteq=not_in_both:newcnf=on:nm=16:rp=on:s2pl=on:sas=z3:slsq=on:slsqc=4:slsql=off:slsqr=33,13:sp=const_min:urr=on:i=248:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_avsq=on:avsql=on:drc=off:ind=struct:indmd=20:kws=precedence:newcnf=on:rp=on:sas=z3:sp=const_max:i=260:si=on:rtra=on_0");
   quick.push("dis+10_1:1_bs=unit_only:fde=unused:fnrw=on:ind=int:indn=off:ins=1:intindstcomp=always:kws=arity:newcnf=on:rp=on:sp=frequency:tac=rule:taea=off:tgt=full:urr=on:i=28:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_abs=on:ev=cautious:gtg=exists_top:ind=struct:newcnf=on:nui=on:s2a=on:sac=on:sas=z3:sik=recursion:i=164:si=on:rtra=on_0");
   quick.push("ott+10_1:1_ind=struct:indstrhyp=on:kws=precedence:s2a=on:s2agt=16:sac=on:sos=all:sp=reverse_arity:spb=intro:i=182:si=on:rtra=on_0");
   quick.push("dis+10_1:1_asg=cautious:ind=both:intindstterm=no_skolems:newcnf=on:norm_ineq=on:rp=on:sac=on:sas=z3:sos=theory:spb=intro:to=lpo:i=260:si=on:rtra=on_0");
   quick.push("ott+10_1:1_drc=off:fs=off:fsr=off:ind=struct:indstrhyp=on:nwc=5.0:s2a=on:sos=on:tar=off:i=133:si=on:rtra=on_0");
   quick.push("lrs-10_1:5_flr=on:fnrw=on:fsr=off:gs=on:ind=struct:indao=on:newcnf=on:plsq=on:plsqc=2:plsqr=2,7:rp=on:sik=recursion:sil=100000:tar=off:uwa=one_side_constant:i=443:si=on:rtra=on_0");
   quick.push("ott+10_1:1_drc=off:gve=cautious:ind=both:kws=inv_frequency:newcnf=on:sik=recursion:sil=100000:sos=on:sp=weighted_frequency:ss=axioms:st=6.0:i=582:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_bd=off:gtg=exists_top:ind=struct:indmd=2:indstrhyp=on:nwc=5.0:s2a=on:s2agt=16:i=103:si=on:rtra=on_0");
   quick.push("ott+21_1:1_asg=cautious:av=off:drc=off:fnrw=on:ins=1:newcnf=on:norm_ineq=on:rp=on:sp=const_min:ss=axioms:taea=off:uwa=interpreted_only:i=96:si=on:rtra=on_0");
   quick.push("dis+21_1:1_alpa=true:amm=off:fnrw=on:gtg=exists_top:gtgl=2:ind=struct:indc=goal:newcnf=on:rp=on:sil=100000:sos=theory:sp=frequency:taea=off:tgt=full:urr=on:i=82:si=on:rtra=on_0");
   quick.push("dis-1011_1:1_erd=off:gtg=exists_sym:gve=cautious:ind=both:indmd=3:indstrhyp=on:kws=inv_frequency:norm_ineq=on:sil=100000:sp=occurrence:spb=intro:ss=axioms:i=86:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_drc=off:gtg=exists_all:gtgl=2:ind=struct:ss=axioms:uwa=one_side_constant:i=86:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_bd=off:ep=RSTC:gtg=exists_all:newcnf=on:nm=10:norm_ineq=on:rp=on:s2agt=32:sac=on:sas=z3:slsq=on:slsqr=151023,1048576:sp=const_max:tac=light:i=161:si=on:rtra=on_0");
   quick.push("dis+2_1:1_fd=preordered:fde=none:gtg=position:newcnf=on:rp=on:sas=z3:sos=theory:sp=unary_frequency:spb=goal:i=295:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_erd=off:gve=cautious:ind=both:newcnf=on:nui=on:updr=off:i=3:si=on:rtra=on_0");
  // Improves by expected 13.741168084071628 probs costing 3857 Mi
  // Sub-schedule for 4000Mi strat cap / 4000Mi overall limit
   quick.push("dis+10_180:31_canc=force:gtg=exists_all:gtgl=4:newcnf=on:rp=on:s2a=on:s2agt=10:sac=on:sas=z3:sos=all:uhcvi=on:i=223:si=on:rtra=on_0");
   quick.push("dis-1011_1:10_bd=preordered:ind=struct:indmd=1:newcnf=on:nui=on:pum=on:sil=100000:i=461:si=on:rtra=on_0");
   quick.push("dis+10_1:1_bs=unit_only:fde=unused:fnrw=on:ind=int:indn=off:ins=1:intindstcomp=always:kws=arity:newcnf=on:rp=on:sp=frequency:tac=rule:taea=off:tgt=full:urr=on:i=28:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_canc=cautious:kws=inv_precedence:nm=0:rp=on:sas=z3:spb=units:updr=off:i=412:si=on:rtra=on_0");
   quick.push("dis+10_1:1_asg=cautious:ind=both:intindstterm=no_skolems:newcnf=on:norm_ineq=on:rp=on:sac=on:sas=z3:sos=theory:spb=intro:to=lpo:i=233:si=on:rtra=on_0");
   quick.push("ott+10_1:1_drc=off:fs=off:fsr=off:ind=struct:indstrhyp=on:nwc=5.0:s2a=on:sos=on:tar=off:i=133:si=on:rtra=on_0");
   quick.push("lrs-10_1:5_flr=on:fnrw=on:fsr=off:gs=on:ind=struct:indao=on:newcnf=on:plsq=on:plsqc=2:plsqr=2,7:rp=on:sik=recursion:sil=100000:tar=off:uwa=one_side_constant:i=389:si=on:rtra=on_0");
   quick.push("dis+10_1:1_avsq=on:avsqr=1,16:drc=off:fd=preordered:ins=1:nm=32:sfv=off:sp=unary_frequency:spb=goal:to=lpo:updr=off:i=1060:si=on:rtra=on_0");
   quick.push("ott+21_1:1_asg=cautious:av=off:drc=off:fnrw=on:ins=1:newcnf=on:norm_ineq=on:rp=on:sp=const_min:ss=axioms:taea=off:uwa=interpreted_only:i=89:si=on:rtra=on_0");
   quick.push("ott+21_3:1_fnrw=on:gtg=exists_sym:gtgl=4:ins=1:newcnf=on:rp=on:sil=100000:ss=axioms:tgt=full:thi=neg_eq:to=lpo:urr=on:i=291:si=on:rtra=on_0");
   quick.push("dis+2_1:1_fd=preordered:fde=none:gtg=position:newcnf=on:rp=on:sas=z3:sos=theory:sp=unary_frequency:spb=goal:i=213:si=on:rtra=on_0");
   quick.push("dis+10_1:1_amm=off:drc=off:gtg=all:gtgl=5:ind=struct:indmd=2:newcnf=on:sos=on:taea=off:tgt=full:i=441:si=on:rtra=on_0");
  // Improves by expected 3.349762257387157 probs costing 3961 Mi
  // Sub-schedule for 8000Mi strat cap / 8000Mi overall limit
   quick.push("dis-1011_1:10_bd=preordered:ind=struct:indmd=1:newcnf=on:nui=on:pum=on:sil=100000:i=461:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_abs=on:anc=all:ev=cautious:kws=inv_frequency:newcnf=on:rp=on:sac=on:sas=z3:spb=goal_then_units:tgt=ground:uwa=interpreted_only:i=681:si=on:rtra=on_0");
   quick.push("dis+10_1:1_asg=cautious:ind=both:intindstterm=no_skolems:newcnf=on:norm_ineq=on:rp=on:sac=on:sas=z3:sos=theory:spb=intro:to=lpo:i=2701:si=on:rtra=on_0");
   quick.push("ott+10_1:1_drc=off:gve=cautious:ind=both:kws=inv_frequency:newcnf=on:sik=recursion:sil=100000:sos=on:sp=weighted_frequency:ss=axioms:st=6.0:i=582:si=on:rtra=on_0");
   quick.push("dis+10_1:1_avsq=on:avsqr=1,16:drc=off:fd=preordered:ins=1:nm=32:sfv=off:sp=unary_frequency:spb=goal:to=lpo:updr=off:i=1060:si=on:rtra=on_0");
   quick.push("lrs+1002_1:3_awrs=decay:fnrw=on:gtg=exists_sym:newcnf=on:nm=32:rp=on:sp=unary_first:tac=rule:taea=off:tar=off:tgt=full:uhcvi=on:uwa=ground:i=734:si=on:rtra=on_0");
   quick.push("dis+10_1:1_amm=off:drc=off:gtg=all:gtgl=5:ind=struct:indmd=2:newcnf=on:sos=on:taea=off:tgt=full:i=441:si=on:rtra=on_0");
  // Improves by expected 1.496372313496297 probs costing 6653 Mi
  // Sub-schedule for 20000Mi strat cap / 20000Mi overall limit
   quick.push("dis+10_1:1_asg=cautious:ind=both:intindstterm=no_skolems:newcnf=on:norm_ineq=on:rp=on:sac=on:sas=z3:sos=theory:spb=intro:to=lpo:i=2701:si=on:rtra=on_0");
   quick.push("ott+1010_9:4_anc=all_dependent:drc=encompass:fsd=on:ind=struct:indao=on:indstrhyp=on:newcnf=on:pum=on:s2a=on:s2agt=32:sos=all:tac=rule:i=4801:si=on:rtra=on_0");
   quick.push("dis+10_1:1_amm=off:drc=off:gtg=all:gtgl=5:ind=struct:indmd=2:newcnf=on:sos=on:taea=off:tgt=full:i=441:si=on:rtra=on_0");
  // Improves by expected 0.4182775034739544 probs costing 7940 Mi

  // Overall score 235.07056943321408 probs on average / budget 24401 Mi
}

void Schedules::getSnakeTptpUnsSchedule(const Shell::Property& property, Schedule& quick) {    
  if (property.hasNumerals() || property.hasInterpretedOperations()) { 
    // problemsARIUNS.txt
    // Champion singleton-schedule for 60000Mi
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=59848:si=on:rawr=on:rtra=on_0");
    // Improves by expected 895.9938356419328 probs costing 59847 Mi
    // Sub-schedule for 50Mi strat cap / 400Mi overall limit
    quick.push("lrs+1010_1:1_aac=none:bce=on:nicw=on:nm=0:plsq=on:plsql=on:sac=on:sos=on:sp=frequency:spb=units:to=lpo:i=34:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_drc=off:flr=on:nwc=2.0:sac=on:urr=ec_only:i=8:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_1:1_erd=off:s2a=on:sac=on:sd=1:sgt=64:sos=on:ss=included:st=3.0:to=lpo:urr=on:i=2:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:2_br=off:bs=unit_only:bsr=unit_only:nwc=5.0:s2a=on:s2agt=32:urr=on:i=37:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_s2a=on:s2agt=10:sgt=8:ss=axioms:i=15:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_5:1_br=off:fde=none:nwc=3.0:sd=1:sgt=10:sos=on:ss=axioms:urr=on:i=32:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:fd=off:fde=none:ins=3:sac=on:sos=on:spb=goal:to=lpo:i=36:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_ep=RST:s2a=on:s2at=5.0:sos=all:i=26:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:8_ep=R:erd=off:fs=off:fsr=off:gve=force:nwc=2.0:uwa=one_side_interpreted:i=2:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_canc=force:tha=some:to=lpo:i=35:si=on:rawr=on:rtra=on_0");
    quick.push("dis+32_1:1_bd=off:nm=4:sos=on:ss=included:i=4:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ep=R:gve=force:plsq=on:plsqr=32,1:uwa=one_side_interpreted:i=2:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:64_nwc=1.4:tha=off:i=21:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+22_1:1_amm=sco:fsr=off:gve=force:sos=on:uwa=all:i=50:si=on:rawr=on:rtra=on_0");
    quick.push("dis+20_1:12_aac=none:acc=model:awrs=converge:fd=preordered:fsr=off:nicw=on:nwc=3.0:s2a=on:s2agt=16:spb=goal:to=lpo:i=2:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ev=force:gve=cautious:tha=off:i=2:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_aac=none:abs=on:er=known:fde=none:fsr=off:nwc=5.0:s2a=on:s2at=4.0:sp=const_frequency:to=lpo:urr=ec_only:i=49:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ss=axioms:st=5.0:tha=off:i=15:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=10:sos=all:ss=axioms:st=5.0:tha=off:i=2:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:5_av=off:nwc=2.0:sos=all:i=15:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:64_nwc=1.4:rp=on:tha=off:i=21:si=on:rawr=on:rtra=on_0");
    // Improves by expected 33.16056460682215 probs costing 389 Mi
    // Sub-schedule for 50Mi strat cap / 400Mi overall limit
    quick.push("dis+2_1:1_av=off:bsr=on:erd=off:s2pl=on:sgt=16:sos=on:sp=frequency:ss=axioms:i=46:si=on:rawr=on:rtra=on_0");
    quick.push("dis+32_1:1_bd=off:nm=4:sos=on:ss=included:i=50:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_1:10_av=off:drc=off:nwc=2.0:sp=reverse_frequency:thsq=on:thsqc=64:thsql=off:i=47:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_br=off:canc=force:drc=off:s2a=on:sos=on:sp=reverse_frequency:urr=on:i=42:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_3:1_ep=RSTC:sos=on:urr=on:i=43:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:64_nwc=1.4:tha=off:i=21:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bd=off:canc=force:ev=cautious:nwc=5.0:i=21:si=on:rawr=on:rtra=on_0");
    quick.push("dis+20_1:12_aac=none:acc=model:awrs=converge:fd=preordered:fsr=off:nicw=on:nwc=3.0:s2a=on:s2agt=16:spb=goal:to=lpo:i=41:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ss=axioms:st=5.0:tha=off:i=15:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_1:1_aac=none:acc=on:add=large:bd=off:bs=unit_only:bsr=on:cond=on:nm=0:sac=on:sd=3:sos=on:ss=axioms:st=2.0:i=47:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:64_nwc=1.4:rp=on:tha=off:i=25:si=on:rawr=on:rtra=on_0");
    // Improves by expected 5.670968176868261 probs costing 387 Mi
    // Sub-schedule for 500Mi strat cap / 4000Mi overall limit
    quick.push("lrs+1010_1:1_aac=none:bce=on:nicw=on:nm=0:plsq=on:plsql=on:sac=on:sos=on:sp=frequency:spb=units:to=lpo:i=148:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_acc=model:br=off:ins=1:newcnf=on:nwc=5.0:s2a=on:sac=on:sp=frequency:to=lpo:urr=on:i=100:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_1:1_bd=off:bsr=unit_only:drc=off:fd=preordered:fsr=off:nwc=3.0:sac=on:to=lpo:urr=on:i=76:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+22_1:1_amm=sco:fsr=off:gve=force:sos=on:uwa=all:i=58:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_thi=all:thigen=on:i=96:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:3_add=large:afr=on:anc=all_dependent:avsq=on:avsqr=21,226:awrs=decay:awrsf=47:br=off:bsd=on:canc=cautious:cond=fast:fd=preordered:fsd=on:fsr=off:gs=on:gve=force:ins=1:lma=on:s2agt=4:s2at=1.9:sas=z3:slsq=on:slsqc=1:slsqr=13,121:sp=reverse_arity:tha=some:to=lpo:uace=off:uhcvi=on:updr=off:urr=ec_only:i=108:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_plsq=on:plsqc=1:plsqr=32,1:tha=off:thi=overlap:i=463:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_4:1_abs=on:afp=20:amm=off:anc=all:bd=off:br=off:canc=force:s2a=on:sas=z3:slsq=on:urr=on:i=494:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_newcnf=on:sas=z3:tgt=ground:tha=off:i=223:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_av=off:br=off:fs=off:fsr=off:tha=off:urr=ec_only:i=343:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_br=off:fs=off:fsr=off:tha=off:urr=ec_only:i=488:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_5:1_aer=off:norm_ineq=on:sas=z3:sos=all:ss=axioms:tha=off:i=150:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_br=off:fde=none:norm_ineq=on:nwc=10.0:sas=z3:slsq=on:slsqc=2:slsql=off:slsqr=1,4:sp=reverse_frequency:i=160:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_bd=off:fde=unused:gsp=on:ins=1:norm_ineq=on:sas=z3:sos=all:tha=off:i=370:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_5:1_norm_ineq=on:sas=z3:sos=all:ss=axioms:tha=off:i=493:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_aac=none:abs=on:bce=on:bd=off:bsr=unit_only:drc=off:fd=preordered:fsd=on:gve=cautious:lcm=reverse:nm=16:plsq=on:plsqc=1:plsqr=232,15:sfv=off:slsq=on:slsql=off:slsqr=3,2:sos=on:sp=weighted_frequency:i=81:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_amm=sco:norm_ineq=on:nwc=3.0:plsq=on:plsqc=2:plsqr=32,1:sas=z3:sp=const_min:tha=off:to=lpo:i=146:si=on:rawr=on:rtra=on_0");
    // Improves by expected 78.30982167660929 probs costing 3980 Mi
    // Sub-schedule for 500Mi strat cap / 4000Mi overall limit
    quick.push("ott+21_1:1_erd=off:s2a=on:sac=on:sd=1:sgt=64:sos=on:ss=included:st=3.0:to=lpo:urr=on:i=211:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_s2a=on:sp=frequency:to=lpo:i=274:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_nm=0:sd=1:ss=axioms:urr=ec_only:i=330:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_erd=off:fs=off:fsr=off:norm_ineq=on:nwc=10.0:s2a=on:s2at=3.0:sas=z3:tha=some:i=294:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+30_1:64_flr=on:sp=frequency:to=lpo:i=213:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_aac=none:abs=on:nicw=on:sac=on:sas=z3:tgt=ground:tha=some:to=lpo:i=374:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_br=off:fs=off:fsr=off:tha=off:urr=ec_only:i=488:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_abs=on:ev=cautious:nwc=10.0:s2a=on:sas=z3:tha=off:thi=all:thigen=on:i=230:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bsr=unit_only:cond=on:flr=on:newcnf=on:nwc=10.0:sas=z3:to=lpo:i=360:si=on:rawr=on:rtra=on_0");
    quick.push("dis+31_1:1_lcm=reverse:norm_ineq=on:nwc=10.0:sas=z3:tha=off:urr=on:i=382:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:fde=none:lwlo=on:nwc=10.0:i=256:si=on:rawr=on:rtra=on_0");
    // Improves by expected 12.840375507795745 probs costing 3900 Mi
    // Sub-schedule for 5000Mi strat cap / 40000Mi overall limit
    quick.push("dis+10_1:1_sgt=16:sos=on:spb=goal:ss=axioms:i=1006:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1004_1:3_av=off:bs=on:plsq=on:i=3721:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_bd=preordered:drc=off:fd=preordered:nwc=5.0:sp=reverse_frequency:i=501:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:1_anc=all:avsq=on:avsqc=1:bsr=unit_only:drc=off:erd=off:fs=off:fsr=off:nwc=3.0:s2a=on:s2at=1.5:sac=on:urr=on:i=1705:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:sd=10:sos=all:ss=axioms:st=4.0:i=2416:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:64_s2a=on:s2agt=16:slsq=on:slsqc=1:slsqr=1,1:i=1683:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_av=off:fsr=off:nm=6:plsq=on:s2a=on:s2at=3.0:slsq=on:slsqc=0:slsqr=1,8:sp=frequency:to=lpo:i=330:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_afp=1:sac=on:sas=z3:tha=off:i=113:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ep=RS:fsr=off:sos=all:i=3217:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_6715:511922_awrs=decay:awrsf=1:bd=preordered:bs=on:drc=off:fd=preordered:nwc=5.0:sp=frequency:spb=goal_then_units:uwa=interpreted_only:i=3528:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:6_aac=none:afr=on:bce=on:bsr=unit_only:canc=cautious:cond=fast:fde=unused:newcnf=on:nwc=3.0:s2a=on:s2agt=40:sas=z3:sfv=off:sp=weighted_frequency:spb=units:tha=off:to=lpo:i=2304:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_abs=on:bd=off:flr=on:nm=0:s2at=3.0:sas=z3:sfv=off:slsq=on:slsqc=2:slsqr=46,31:sp=const_frequency:tgt=ground:tha=some:thi=overlap:thitd=on:thsq=on:thsqc=32:thsqd=32:thsqr=7,4:i=3780:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_newcnf=on:sas=z3:tgt=ground:tha=off:i=238:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_aac=none:abs=on:nicw=on:sac=on:sas=z3:tgt=ground:tha=some:to=lpo:i=656:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=485:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_aac=none:abs=on:bd=off:fd=off:nm=0:sas=z3:sims=off:tha=off:to=lpo:i=1302:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_4:1_abs=on:afp=20:amm=off:anc=all:bd=off:br=off:canc=force:s2a=on:sas=z3:slsq=on:urr=on:i=980:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_br=off:fs=off:fsr=off:tha=off:urr=ec_only:i=638:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_137062:920759_aac=none:abs=on:amm=sco:anc=none:asg=cautious:atotf=0.5:avsq=on:avsqc=2:avsqr=383,440:bce=on:bsd=on:erd=off:fde=unused:gs=on:gve=cautious:newcnf=on:nwc=3.3:sac=on:sas=z3:sfv=off:skr=on:spb=goal:tgt=ground:thsq=on:thsqc=128:thsql=off:uwa=all:i=947:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1024_drc=off:fde=none:gve=force:nm=4:norm_ineq=on:sas=z3:sos=all:sp=const_min:spb=non_intro:to=lpo:uwa=one_side_constant:i=691:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:128_asg=cautious:drc=off:fde=none:gve=force:norm_ineq=on:sas=z3:sos=all:sp=reverse_arity:spb=intro:ss=axioms:to=lpo:uwa=one_side_constant:i=370:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_bd=off:fde=unused:gsp=on:ins=1:norm_ineq=on:sas=z3:sos=all:tha=off:i=361:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_bce=on:drc=off:erd=off:gve=force:ins=2:norm_ineq=on:sac=on:sp=frequency:tha=some:urr=on:i=3058:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_5:1_norm_ineq=on:sas=z3:sos=all:ss=axioms:tha=off:i=1198:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_avsq=on:avsql=on:avsqr=1,16:norm_ineq=on:nwc=10.0:plsq=on:sas=z3:tha=off:urr=on:i=2501:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:fde=none:lwlo=on:nwc=10.0:i=256:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bd=preordered:sd=2:sos=all:ss=axioms:i=217:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_1:1_aac=none:amm=off:bd=off:fsr=off:sas=z3:sos=all:sp=const_frequency:tha=off:i=1168:si=on:rawr=on:rtra=on_0");
    // Improves by expected 26.727843621218934 probs costing 39932 Mi
    // Sub-schedule for 5000Mi strat cap / 40000Mi overall limit
    quick.push("dis+10_1:1_sgt=16:sos=on:spb=goal:ss=axioms:i=1006:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1004_1:3_av=off:bs=on:plsq=on:i=4966:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_18762:894869_awrs=decay:awrsf=8:bsd=on:drc=off:fsr=off:irw=on:newcnf=on:slsq=on:slsqc=1:slsqr=76,61:i=4835:si=on:rawr=on:rtra=on_0");
    quick.push("ott+0_1:128_afr=on:amm=sco:anc=none:awrs=converge:awrsf=110:bsd=on:cond=fast:etr=on:fde=unused:flr=on:fsd=on:gve=force:irw=on:norm_ineq=on:sas=z3:sos=all:spb=units:tha=off:thi=strong:to=lpo:uwa=one_side_interpreted:i=3932:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:6_aac=none:afr=on:bce=on:bsr=unit_only:canc=cautious:cond=fast:fde=unused:newcnf=on:nwc=3.0:s2a=on:s2agt=40:sas=z3:sfv=off:sp=weighted_frequency:spb=units:tha=off:to=lpo:i=1742:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_abs=on:bd=off:flr=on:nm=0:s2at=3.0:sas=z3:sfv=off:slsq=on:slsqc=2:slsqr=46,31:sp=const_frequency:tgt=ground:tha=some:thi=overlap:thitd=on:thsq=on:thsqc=32:thsqd=32:thsqr=7,4:i=3843:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_137062:920759_aac=none:abs=on:amm=sco:anc=none:asg=cautious:atotf=0.5:avsq=on:avsqc=2:avsqr=383,440:bce=on:bsd=on:erd=off:fde=unused:gs=on:gve=cautious:newcnf=on:nwc=3.3:sac=on:sas=z3:sfv=off:skr=on:spb=goal:tgt=ground:thsq=on:thsqc=128:thsql=off:uwa=all:i=947:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:14_awrs=converge:sp=unary_first:tgt=ground:i=3622:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_9:8_amm=off:bsd=on:etr=on:fsd=on:fsr=off:lma=on:newcnf=on:nm=0:nwc=3.0:s2a=on:s2agt=10:sas=z3:tha=some:i=4725:si=on:rawr=on:rtra=on_0");
    quick.push("dis+31_1:1_lcm=reverse:norm_ineq=on:nwc=10.0:sas=z3:tha=off:urr=on:i=1518:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_avsq=on:avsql=on:avsqr=1,16:norm_ineq=on:nwc=10.0:plsq=on:sas=z3:tha=off:urr=on:i=2661:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_2:1_add=large:afp=4000:newcnf=on:sd=1:sos=on:sp=const_min:ss=axioms:i=1324:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_1:1_aac=none:amm=off:bd=off:fsr=off:sas=z3:sos=all:sp=const_frequency:tha=off:i=1168:si=on:rawr=on:rtra=on_0");
    // Improves by expected 3.798874060365022 probs costing 36276 Mi
    // Sub-schedule for 50000Mi strat cap / 400000Mi overall limit
    quick.push("dis+1004_1:3_av=off:bs=on:plsq=on:i=11321:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:sd=10:sos=all:ss=axioms:st=4.0:i=12082:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_3:1_abs=on:ep=RST:newcnf=on:nm=2:sas=z3:sd=1:sos=all:ss=included:to=lpo:i=31695:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_nm=0:sd=1:ss=axioms:urr=ec_only:i=7145:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:ep=RSTC:plsq=on:plsqc=1:plsqr=32,1:urr=on:i=48352:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:16_ss=axioms:st=3.0:i=48076:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:1_ep=RS:fs=off:fsr=off:s2a=on:s2at=1.5:sac=on:sos=all:updr=off:i=24952:si=on:rawr=on:rtra=on_0");
    quick.push("ott+0_1:128_afr=on:amm=sco:anc=none:awrs=converge:awrsf=110:bsd=on:cond=fast:etr=on:fde=unused:flr=on:fsd=on:gve=force:irw=on:norm_ineq=on:sas=z3:sos=all:spb=units:tha=off:thi=strong:to=lpo:uwa=one_side_interpreted:i=17722:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+35_1:1_aac=none:abs=on:amm=off:norm_ineq=on:s2a=on:s2at=3.0:tha=off:i=25691:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:6_aac=none:afr=on:bce=on:bsr=unit_only:canc=cautious:cond=fast:fde=unused:newcnf=on:nwc=3.0:s2a=on:s2agt=40:sas=z3:sfv=off:sp=weighted_frequency:spb=units:tha=off:to=lpo:i=1742:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_abs=on:bd=off:flr=on:nm=0:s2at=3.0:sas=z3:sfv=off:slsq=on:slsqc=2:slsqr=46,31:sp=const_frequency:tgt=ground:tha=some:thi=overlap:thitd=on:thsq=on:thsqc=32:thsqd=32:thsqr=7,4:i=31719:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_aac=none:abs=on:bd=off:fd=off:nm=0:sas=z3:sims=off:tha=off:to=lpo:i=12098:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ev=force:newcnf=on:sas=z3:spb=goal:tgt=full:tha=off:uwa=ground:i=7522:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_abs=on:afp=1000:nicw=on:sas=z3:tgt=ground:tha=off:uwa=all:i=9256:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+31_1:3_abs=on:add=large:afp=329:afq=1.2:anc=none:avsq=on:avsqr=160,201:awrs=decay:bce=on:bsr=unit_only:canc=cautious:etr=on:ev=force:flr=on:fs=off:fsd=on:fsr=off:irw=on:lcm=reverse:newcnf=on:nicw=on:nwc=1.55:pum=on:rnwc=on:s2agt=32:sas=z3:sffsmt=on:sims=off:skr=on:slsq=on:slsqc=2:slsqr=433504,723351:sp=unary_first:spb=goal_then_units:tgt=full:tha=some:to=lpo:uhcvi=on:uwa=one_side_constant:i=7507:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_9:8_amm=off:bsd=on:etr=on:fsd=on:fsr=off:lma=on:newcnf=on:nm=0:nwc=3.0:s2a=on:s2agt=10:sas=z3:tha=some:i=4725:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_avsq=on:avsql=on:avsqr=1,16:norm_ineq=on:nwc=10.0:plsq=on:sas=z3:tha=off:urr=on:i=6461:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_5:1_drc=off:kws=inv_arity_squared:nwc=5.0:plsq=on:plsqc=1:plsqr=32,1:s2a=on:s2at=2.1:urr=ec_only:i=11248:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=10:sos=all:ss=axioms:st=5.0:tha=off:i=10523:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_2:1_add=large:afp=4000:newcnf=on:sd=1:sos=on:sp=const_min:ss=axioms:i=1324:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_afq=1.0:bd=off:bsr=unit_only:irw=on:i=49169:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_nm=0:sd=4:sos=on:ss=axioms:st=3.0:i=6824:si=on:rawr=on:rtra=on_0");
    // Improves by expected 42.55703705816949 probs costing 387132 Mi
    // Sub-schedule for 50000Mi strat cap / 400000Mi overall limit
    quick.push("lrs+10_1:1_av=off:sd=10:sos=all:ss=axioms:st=4.0:i=12082:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_3:1_abs=on:ep=RST:newcnf=on:nm=2:sas=z3:sd=1:sos=all:ss=included:to=lpo:i=20746:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1024_br=off:ep=RSTC:urr=on:i=47953:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:1_ep=RS:fs=off:fsr=off:s2a=on:s2at=1.5:sac=on:sos=all:updr=off:i=18577:si=on:rawr=on:rtra=on_0");
    quick.push("ott+0_1:128_afr=on:amm=sco:anc=none:awrs=converge:awrsf=110:bsd=on:cond=fast:etr=on:fde=unused:flr=on:fsd=on:gve=force:irw=on:norm_ineq=on:sas=z3:sos=all:spb=units:tha=off:thi=strong:to=lpo:uwa=one_side_interpreted:i=17722:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_5:1_av=off:awrs=decay:awrsf=16:cond=on:fd=preordered:sfv=off:sp=const_frequency:thi=neg_eq:thsq=on:thsqc=16:thsqd=64:i=26841:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_abs=on:bd=off:flr=on:nm=0:s2at=3.0:sas=z3:sfv=off:slsq=on:slsqc=2:slsqr=46,31:sp=const_frequency:tgt=ground:tha=some:thi=overlap:thitd=on:thsq=on:thsqc=32:thsqd=32:thsqr=7,4:i=13722:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=30560:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_aac=none:abs=on:bd=off:fd=off:nm=0:sas=z3:sims=off:tha=off:to=lpo:i=12098:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ev=force:newcnf=on:sas=z3:spb=goal:tgt=full:tha=off:uwa=ground:i=7522:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+31_1:3_abs=on:add=large:afp=329:afq=1.2:anc=none:avsq=on:avsqr=160,201:awrs=decay:bce=on:bsr=unit_only:canc=cautious:etr=on:ev=force:flr=on:fs=off:fsd=on:fsr=off:irw=on:lcm=reverse:newcnf=on:nicw=on:nwc=1.55:pum=on:rnwc=on:s2agt=32:sas=z3:sffsmt=on:sims=off:skr=on:slsq=on:slsqc=2:slsqr=433504,723351:sp=unary_first:spb=goal_then_units:tgt=full:tha=some:to=lpo:uhcvi=on:uwa=one_side_constant:i=7507:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_avsq=on:avsql=on:avsqr=1,16:norm_ineq=on:nwc=10.0:plsq=on:sas=z3:tha=off:urr=on:i=2501:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=10:sos=all:ss=axioms:st=5.0:tha=off:i=10523:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:3_afp=4000:anc=none:bce=on:bd=off:sac=on:sd=10:ss=axioms:st=5.0:tha=off:urr=ec_only:i=18001:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_afq=1.0:bd=off:bsr=unit_only:irw=on:i=49169:si=on:rawr=on:rtra=on_0");
    quick.push("ott+2_1:64_afp=40000:bd=off:irw=on:i=49900:si=on:rawr=on:rtra=on_0");
    // Improves by expected 3.234326331534754 probs costing 345408 Mi
    // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
    quick.push("lrs+10_1:1_av=off:sd=10:sos=all:ss=axioms:st=4.0:i=12082:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_3:1_abs=on:ep=RST:newcnf=on:nm=2:sas=z3:sd=1:sos=all:ss=included:to=lpo:i=67061:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:1_ep=RS:fs=off:fsr=off:s2a=on:s2at=1.5:sac=on:sos=all:updr=off:i=18577:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_5:1_av=off:awrs=decay:awrsf=16:cond=on:fd=preordered:sfv=off:sp=const_frequency:thi=neg_eq:thsq=on:thsqc=16:thsqd=64:i=26841:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=62922:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+20_1:1_fsr=off:kws=precedence:i=115780:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=10:sos=all:ss=axioms:st=5.0:tha=off:i=10523:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:1_av=off:nwc=2.0:sos=theory:sp=const_frequency:updr=off:urr=ec_only:i=212020:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_afq=1.0:bd=off:bsr=unit_only:irw=on:i=62001:si=on:rawr=on:rtra=on_0");
    quick.push("ott+2_1:64_afp=40000:bd=off:irw=on:i=77001:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:rp=on:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=474375:si=on:rawr=on:rtra=on_0");
    // Improves by expected 3.384799751855749 probs costing 1139172 Mi
    // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
    quick.push("lrs+10_1:1_av=off:sd=10:sos=all:ss=axioms:st=4.0:i=12082:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_3:1_abs=on:ep=RST:newcnf=on:nm=2:sas=z3:sd=1:sos=all:ss=included:to=lpo:i=67061:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+20_1:1_fsr=off:kws=precedence:i=115780:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=10:sos=all:ss=axioms:st=5.0:tha=off:i=10523:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:1_av=off:nwc=2.0:sos=theory:sp=const_frequency:updr=off:urr=ec_only:i=212020:si=on:rawr=on:rtra=on_0");
    // Improves by expected 0.7984370878488387 probs costing 417461 Mi
    // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
    quick.push("lrs+10_1:1_av=off:sd=10:sos=all:ss=axioms:st=4.0:i=12082:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_3:1_abs=on:ep=RST:newcnf=on:nm=2:sas=z3:sd=1:sos=all:ss=included:to=lpo:i=67061:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=10:sos=all:ss=axioms:st=5.0:tha=off:i=10523:si=on:rawr=on:rtra=on_0");
    // Improves by expected 0.3879708469664596 probs costing 89663 Mi
    // Overall score 1106.8648543679876 probs on average / budget 2523547 Mi
  } else if (property.category() == Property::Category::UEQ) {
    // problemsUEQUNS.txt
    // Champion singleton-schedule for 100000Mi
    quick.push("dis+1002_1:12_drc=off:fd=preordered:tgt=full:i=99788:si=on:rawr=on:rtra=on_0");
    // Improves by expected 749.9639594667524 probs costing 99787 Mi
    // Sub-schedule for 50Mi strat cap / 400Mi overall limit
    quick.push("lrs+10_1:16_awrs=converge:awrsf=40:br=off:ep=RSTC:flr=on:gsp=on:nwc=3.0:sos=on:urr=on:i=10:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1004_1:734_av=off:awrs=converge:awrsf=70:br=off:ep=RSTC:erd=off:gs=on:nwc=3.0:s2a=on:s2agt=16:sp=occurrence:updr=off:urr=on:i=37:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_amm=off:drc=off:sp=reverse_frequency:spb=goal_then_units:to=lpo:i=6:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_drc=off:fd=preordered:plsq=on:sp=occurrence:to=lpo:i=48:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:ep=RSTC:sos=all:urr=on:i=20:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_avsq=on:avsql=on:bsr=unit_only:drc=off:fsr=off:inw=on:nwc=10.0:rnwc=on:sgt=16:slsq=on:slsqc=0:slsql=off:slsqr=211,119:sp=reverse_frequency:spb=goal_then_units:ss=included:st=2.0:to=lpo:i=7:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_3:1_ep=RSTC:sos=on:urr=on:i=33:si=on:rawr=on:rtra=on_0");
    quick.push("dis+31_8:1_br=off:fd=off:gs=on:lcm=reverse:nm=16:nwc=5.0:sp=reverse_arity:urr=on:i=37:si=on:rawr=on:rtra=on_0");
    // Improves by expected 6.987615834780721 probs costing 190 Mi
    // Sub-schedule for 50Mi strat cap / 400Mi overall limit
    quick.push("lrs+10_1:16_awrs=converge:awrsf=40:br=off:ep=RSTC:flr=on:gsp=on:nwc=3.0:sos=on:urr=on:i=46:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1004_1:734_av=off:awrs=converge:awrsf=70:br=off:ep=RSTC:erd=off:gs=on:nwc=3.0:s2a=on:s2agt=16:sp=occurrence:updr=off:urr=on:i=37:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_drc=off:fd=preordered:plsq=on:sp=occurrence:to=lpo:i=48:si=on:rawr=on:rtra=on_0");
    // Improves by expected 0.5519291203350296 probs costing 128 Mi
    // Sub-schedule for 500Mi strat cap / 4000Mi overall limit
    quick.push("dis+10_1:1024_anc=all:drc=off:flr=on:fsr=off:sac=on:urr=on:i=292:si=on:rawr=on:rtra=on_0");
    quick.push("dis+2_1:1024_abs=on:alpa=false:anc=all_dependent:avsq=on:bce=on:drc=off:newcnf=on:slsq=on:slsqc=0:slsqr=1,1:sp=reverse_arity:i=353:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:128_plsq=on:plsqc=2:s2a=on:ss=axioms:st=1.5:urr=on:i=321:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:7_drc=off:fd=preordered:plsq=on:sp=reverse_frequency:to=lpo:i=212:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_drc=off:fd=preordered:plsq=on:sp=occurrence:to=lpo:i=48:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:flr=on:slsq=on:slsqc=1:sp=frequency:urr=on:i=257:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_asg=cautious:bsr=on:cond=on:drc=off:etr=on:fd=preordered:gs=on:plsq=on:plsqr=388,511:slsq=on:slsqc=1:slsqr=21,31:urr=on:i=439:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:128_bd=off:drc=off:fd=preordered:nwc=1.6:urr=on:i=103:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1024_drc=off:i=388:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:64_fd=off:nm=0:nwc=5.0:i=481:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_5:1_br=off:ep=RSTC:sos=all:urr=on:i=267:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:8_aac=none:bs=unit_only:er=filter:fd=off:nwc=5.0:s2pl=no:i=111:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:drc=off:slsq=on:slsqc=1:slsqr=29,16:sp=reverse_frequency:to=lpo:i=248:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:2_bd=preordered:drc=off:fd=preordered:fde=unused:sp=const_min:to=lpo:i=177:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1024_av=off:bd=preordered:drc=off:nwc=3.0:rp=on:thsq=on:thsqc=64:thsqd=32:to=lpo:i=267:si=on:rawr=on:rtra=on_0");
    // Improves by expected 30.8243592800958 probs costing 3949 Mi
    // Sub-schedule for 500Mi strat cap / 4000Mi overall limit
    quick.push("lrs+10_1:128_awrs=converge:awrsf=8:bd=off:drc=off:slsq=on:slsqc=1:slsql=off:slsqr=40,29:i=495:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:16_awrs=converge:awrsf=40:br=off:ep=RSTC:flr=on:gsp=on:nwc=3.0:sos=on:urr=on:i=381:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_drc=off:fd=preordered:plsq=on:sp=occurrence:to=lpo:i=48:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:flr=on:slsq=on:slsqc=1:sp=frequency:urr=on:i=257:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:3_acc=on:amm=off:avsq=on:avsqr=1729,253:bs=on:drc=off:fsr=off:lwlo=on:sac=on:slsq=on:slsqc=2:slsql=off:slsqr=1,8:sp=weighted_frequency:i=463:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_avsq=on:avsql=on:bsr=unit_only:drc=off:fsr=off:inw=on:nwc=10.0:rnwc=on:sgt=16:slsq=on:slsqc=0:slsql=off:slsqr=211,119:sp=reverse_frequency:spb=goal_then_units:ss=included:st=2.0:to=lpo:i=292:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_asg=cautious:bsr=on:cond=on:drc=off:etr=on:fd=preordered:gs=on:plsq=on:plsqr=388,511:slsq=on:slsqc=1:slsqr=21,31:urr=on:i=439:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_bd=preordered:drc=off:fde=unused:slsq=on:slsqr=10,31:sp=const_min:tgt=ground:to=lpo:urr=ec_only:i=402:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:512_av=off:awrs=converge:awrsf=8:bd=preordered:br=off:bsr=unit_only:drc=off:erd=off:foolp=on:fsd=on:gve=cautious:irw=on:kmz=on:kws=arity_squared:lcm=reverse:newcnf=on:nwc=5.0:plsq=on:plsqc=2:plsql=on:plsqr=9798671,477100:slsq=on:slsqc=1:slsqr=1,16:sp=weighted_frequency:spb=intro:tgt=full:updr=off:urr=on:uwa=ground:i=496:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_drc=off:s2a=on:s2agt=8:sp=reverse_arity:to=lpo:i=312:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:drc=off:slsq=on:slsqc=1:slsqr=29,16:sp=reverse_frequency:to=lpo:i=248:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:2_bd=preordered:drc=off:fd=preordered:fde=unused:sp=const_min:to=lpo:i=177:si=on:rawr=on:rtra=on_0");
    // Improves by expected 4.3396803531853605 probs costing 3998 Mi
    // Sub-schedule for 5000Mi strat cap / 40000Mi overall limit
    quick.push("lrs+10_1:128_awrs=converge:awrsf=8:bd=off:drc=off:slsq=on:slsqc=1:slsql=off:slsqr=40,29:i=1598:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:16_awrs=converge:awrsf=40:br=off:ep=RSTC:flr=on:gsp=on:nwc=3.0:sos=on:urr=on:i=381:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_s2a=on:s2agt=10:sgt=8:ss=axioms:i=1242:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:92_abs=on:amm=sco:anc=all:avsq=on:avsqc=1:avsql=on:avsqr=41,14:awrs=converge:awrsf=170:bd=preordered:bs=on:bsr=unit_only:erd=off:fd=preordered:irw=on:lcm=reverse:lwlo=on:newcnf=on:nicw=on:nwc=4.0:s2a=on:s2agt=64:sas=z3:sims=off:sp=frequency:to=lpo:urr=on:i=629:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_2:1_bd=preordered:bsr=unit_only:drc=off:fd=preordered:fde=none:lwlo=on:sp=reverse_frequency:ss=axioms:st=3.0:to=lpo:i=1575:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:8_anc=all_dependent:atotf=0.2:drc=off:fde=unused:nicw=on:nwc=3.0:sas=z3:slsq=on:slsqc=1:slsqr=3,2:sp=reverse_frequency:i=4955:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_1:1_bd=off:bsr=unit_only:drc=off:fd=preordered:fsr=off:nwc=3.0:sac=on:to=lpo:urr=on:i=1429:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:173_acc=on:aer=off:alpa=true:anc=none:avsq=on:avsqr=497233,912204:awrs=decay:awrsf=4:bce=on:bs=on:bsd=on:cond=on:drc=off:erd=off:flr=on:gsp=on:nicw=on:nm=16:nwc=3.0:sd=2:sfv=off:skr=on:sp=reverse_arity:ss=axioms:st=2.0:updr=off:urr=ec_only:i=2989:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_6339:827045_acc=on:anc=all:awrs=decay:awrsf=1:bce=on:br=off:bs=unit_only:cond=on:foolp=on:nicw=on:nwc=2.0:s2a=on:s2agt=8:sd=1:sgt=16:sp=occurrence:ss=axioms:st=1.2:updr=off:urr=on:uwa=all:i=2096:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:16_drc=off:fde=none:spb=goal_then_units:to=lpo:i=1345:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_avsq=on:avsql=on:bsr=unit_only:drc=off:fsr=off:inw=on:nwc=10.0:rnwc=on:sgt=16:slsq=on:slsqc=0:slsql=off:slsqr=211,119:sp=reverse_frequency:spb=goal_then_units:ss=included:st=2.0:to=lpo:i=290:si=on:rawr=on:rtra=on_0");
    quick.push("dis+2_1:1_av=off:flr=on:plsq=on:plsqc=1:plsqr=32,1:sp=reverse_frequency:to=lpo:urr=ec_only:uwa=all:i=4705:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_bd=preordered:drc=off:fde=unused:slsq=on:slsqr=10,31:sp=const_min:tgt=ground:to=lpo:urr=ec_only:i=2797:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:32_tgt=ground:i=4929:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_drc=off:s2a=on:s2agt=8:sp=reverse_arity:to=lpo:i=1841:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:16_acc=on:drc=off:fd=preordered:fsd=on:nwc=2.0:slsq=on:slsqc=2:slsql=off:slsqr=1,16:thsq=on:thsqc=16:thsqd=16:urr=on:i=4917:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:drc=off:slsq=on:slsqc=1:slsqr=29,16:sp=reverse_frequency:to=lpo:i=248:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_2:1_av=off:irw=on:lwlo=on:newcnf=on:nm=16:nwc=2:sd=4:sp=occurrence:ss=axioms:st=3.0:i=1314:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1024_av=off:bd=preordered:drc=off:nwc=3.0:rp=on:thsq=on:thsqc=64:thsqd=32:to=lpo:i=620:si=on:rawr=on:rtra=on_0");
    // Improves by expected 33.962918739430066 probs costing 39881 Mi
    // Sub-schedule for 5000Mi strat cap / 40000Mi overall limit
    quick.push("lrs+10_1:16_awrs=converge:awrsf=40:br=off:ep=RSTC:flr=on:gsp=on:nwc=3.0:sos=on:urr=on:i=381:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_s2a=on:s2agt=10:sgt=8:ss=axioms:i=1242:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_8:1_bd=preordered:drc=off:fd=preordered:sp=reverse_frequency:i=4700:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:12_drc=off:ins=1:sp=frequency:spb=goal_then_units:i=4963:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:64_s2a=on:s2agt=16:slsq=on:slsqc=1:slsqr=1,1:i=3884:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_1:1_bd=off:bsr=unit_only:drc=off:fd=preordered:fsr=off:nwc=3.0:sac=on:to=lpo:urr=on:i=875:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=2970:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_avsq=on:avsql=on:bsr=unit_only:drc=off:fsr=off:inw=on:nwc=10.0:rnwc=on:sgt=16:slsq=on:slsqc=0:slsql=off:slsqr=211,119:sp=reverse_frequency:spb=goal_then_units:ss=included:st=2.0:to=lpo:i=290:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_26459:191296_av=off:awrs=converge:awrsf=30:bd=preordered:bs=unit_only:drc=off:etr=on:flr=on:lwlo=on:nwc=5.0:plsq=on:plsqc=1:plsql=on:plsqr=1,32:skr=on:slsq=on:slsqr=18,107:sp=const_min:tgt=ground:to=lpo:urr=ec_only:i=3607:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_drc=off:fd=preordered:tgt=full:to=lpo:i=2934:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:16_acc=on:drc=off:fd=preordered:fsd=on:nwc=2.0:slsq=on:slsqc=2:slsql=off:slsqr=1,16:thsq=on:thsqc=16:thsqd=16:urr=on:i=4940:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1024_drc=off:ins=1:nwc=5.0:slsq=on:slsqc=1:slsql=off:slsqr=1,8:urr=on:uwa=all:i=4546:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_2:1_av=off:irw=on:lwlo=on:newcnf=on:nm=16:nwc=2:sd=4:sp=occurrence:ss=axioms:st=3.0:i=1314:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_8:1_aac=none:anc=all_dependent:lwlo=on:nm=2:nwc=10.0:sac=on:sos=all:i=3317:si=on:rawr=on:rtra=on_0");
    // Improves by expected 9.084872377925532 probs costing 39949 Mi
    // Sub-schedule for 50000Mi strat cap / 400000Mi overall limit
    quick.push("lrs+10_1:16_awrs=converge:awrsf=40:br=off:ep=RSTC:flr=on:gsp=on:nwc=3.0:sos=on:urr=on:i=381:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:227_abs=on:amm=off:avsq=on:avsqc=1:avsqr=97,32:awrs=converge:awrsf=256:bsr=unit_only:drc=off:fd=preordered:plsq=on:plsqc=1:plsql=on:plsqr=27942579,963352:sas=z3:slsq=on:slsqc=1:slsql=off:slsqr=307,512:sp=occurrence:ss=axioms:st=3.0:i=5027:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:92_abs=on:amm=sco:anc=all:avsq=on:avsqc=1:avsql=on:avsqr=41,14:awrs=converge:awrsf=170:bd=preordered:bs=on:bsr=unit_only:erd=off:fd=preordered:irw=on:lcm=reverse:lwlo=on:newcnf=on:nicw=on:nwc=4.0:s2a=on:s2agt=64:sas=z3:sims=off:sp=frequency:to=lpo:urr=on:i=1293:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:12_drc=off:ins=1:sp=frequency:spb=goal_then_units:i=7928:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_av=off:bd=preordered:bsd=on:drc=off:etr=on:fd=preordered:fsr=off:ins=1:lma=on:slsq=on:slsqc=1:slsql=off:slsqr=9,8:sp=frequency:spb=goal:urr=ec_only:i=3180:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_bd=preordered:drc=off:fd=preordered:nwc=5.0:sp=reverse_frequency:i=20527:si=on:rawr=on:rtra=on_0");
    quick.push("dis+0_46177:627804_av=off:awrs=decay:awrsf=350:bs=unit_only:s2a=on:s2at=3.2:skr=on:slsq=on:slsqc=0:slsql=off:slsqr=10,103:sp=reverse_arity:urr=ec_only:i=9439:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:64_s2a=on:s2agt=16:slsq=on:slsqc=1:slsqr=1,1:i=5084:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_1:1_bd=off:bsr=unit_only:drc=off:fd=preordered:fsr=off:nwc=3.0:sac=on:to=lpo:urr=on:i=875:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:128_plsq=on:plsqc=2:s2a=on:ss=axioms:st=1.5:urr=on:i=6250:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_6339:827045_acc=on:anc=all:awrs=decay:awrsf=1:bce=on:br=off:bs=unit_only:cond=on:foolp=on:nicw=on:nwc=2.0:s2a=on:s2agt=8:sd=1:sgt=16:sp=occurrence:ss=axioms:st=1.2:updr=off:urr=on:uwa=all:i=3068:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_avsq=on:avsql=on:bsr=unit_only:drc=off:fsr=off:inw=on:nwc=10.0:rnwc=on:sgt=16:slsq=on:slsqc=0:slsql=off:slsqr=211,119:sp=reverse_frequency:spb=goal_then_units:ss=included:st=2.0:to=lpo:i=290:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_3:1_bd=off:fde=none:lwlo=on:i=15258:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:4_awrs=converge:drc=off:lwlo=on:sp=reverse_frequency:urr=ec_only:i=36973:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:6_bd=off:drc=off:tgt=full:i=26171:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1024_drc=off:sp=unary_frequency:tgt=full:to=lpo:i=34839:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_bd=preordered:drc=off:fde=unused:slsq=on:slsqr=10,31:sp=const_min:tgt=ground:to=lpo:urr=ec_only:i=29065:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_kws=precedence:lwlo=on:tgt=ground:i=25210:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:512_drc=off:fd=preordered:ins=2:kws=precedence:s2a=on:sp=unary_first:spb=intro:tgt=ground:i=21216:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:32_tgt=ground:i=34326:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:128_drc=off:ins=1:sp=const_frequency:tgt=ground:i=47220:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+33_1:4_lwlo=on:s2a=on:tgt=ground:i=41523:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:3_drc=off:fd=off:nwc=5.0:plsq=on:plsql=on:slsq=on:slsql=off:slsqr=17,16:sp=occurrence:i=7342:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:16_acc=on:drc=off:fd=preordered:fsd=on:nwc=2.0:slsq=on:slsqc=2:slsql=off:slsqr=1,16:thsq=on:thsqc=16:thsqd=16:urr=on:i=5576:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:5_bs=unit_only:drc=off:ins=1:nwc=2.16:rnwc=on:slsq=on:slsqr=13,149:sp=const_min:tgt=ground:to=lpo:uwa=interpreted_only:i=5261:si=on:rawr=on:rtra=on_0");
    // Improves by expected 53.77302529552434 probs costing 393297 Mi
    // Sub-schedule for 100000Mi strat cap / 800000Mi overall limit
    quick.push("dis+1011_1:227_abs=on:amm=off:avsq=on:avsqc=1:avsqr=97,32:awrs=converge:awrsf=256:bsr=unit_only:drc=off:fd=preordered:plsq=on:plsqc=1:plsql=on:plsqr=27942579,963352:sas=z3:slsq=on:slsqc=1:slsql=off:slsqr=307,512:sp=occurrence:ss=axioms:st=3.0:i=4918:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:128_plsq=on:plsqc=2:s2a=on:ss=axioms:st=1.5:urr=on:i=5834:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:1024_gsp=on:newcnf=on:nwc=2.0:s2a=on:s2at=3.0:sp=reverse_arity:spb=goal_then_units:updr=off:i=46881:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1024_afp=20:afq=2.0:anc=all:bd=preordered:bs=unit_only:drc=off:sac=on:sos=on:to=lpo:i=54362:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:128_awrs=converge:bd=preordered:drc=off:sp=reverse_frequency:to=lpo:i=16945:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_add=large:bd=off:bs=on:drc=off:fd=preordered:gs=on:ins=1:nwc=10.0:s2a=on:sp=reverse_arity:to=lpo:uwa=one_side_interpreted:i=60637:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:12_drc=off:fsr=off:urr=ec_only:i=85561:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:6_bd=off:drc=off:tgt=full:i=26171:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:2_drc=off:fd=preordered:kws=inv_arity:tgt=full:i=20514:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:512_drc=off:fd=preordered:ins=2:kws=precedence:s2a=on:sp=unary_first:spb=intro:tgt=ground:i=7254:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:128_drc=off:ins=1:sp=const_frequency:tgt=ground:i=63326:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_1:1024_bd=off:bs=on:drc=off:kmz=on:kws=precedence:plsq=on:spb=goal:tgt=full:i=93622:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:3_drc=off:fd=off:nwc=5.0:plsq=on:plsql=on:slsq=on:slsql=off:slsqr=17,16:sp=occurrence:i=7301:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_13:991_awrs=decay:awrsf=1:bd=preordered:drc=off:fd=preordered:sp=const_frequency:spb=goal_then_units:uwa=all:i=23094:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:128_aac=none:acc=on:amm=off:atotf=0.1:bd=preordered:drc=off:fd=preordered:fde=none:gs=on:nicw=on:s2a=on:s2at=5.0:slsq=on:sp=const_max:spb=non_intro:tgt=ground:to=lpo:i=87610:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:5_bs=unit_only:drc=off:ins=1:nwc=2.16:rnwc=on:slsq=on:slsqr=13,149:sp=const_min:tgt=ground:to=lpo:uwa=interpreted_only:i=98883:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:rp=on:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=96639:si=on:rawr=on:rtra=on_0");
    // Improves by expected 23.057848333826335 probs costing 799535 Mi
    // Sub-schedule for 150000Mi strat cap / 1200000Mi overall limit
    quick.push("dis+1011_1:227_abs=on:amm=off:avsq=on:avsqc=1:avsqr=97,32:awrs=converge:awrsf=256:bsr=unit_only:drc=off:fd=preordered:plsq=on:plsqc=1:plsql=on:plsqr=27942579,963352:sas=z3:slsq=on:slsqc=1:slsql=off:slsqr=307,512:sp=occurrence:ss=axioms:st=3.0:i=4918:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:64_atotf=0.5:s2a=on:s2at=1.5:urr=on:i=43128:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:128_plsq=on:plsqc=2:s2a=on:ss=axioms:st=1.5:urr=on:i=5834:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:14_drc=off:nwc=10.0:to=lpo:i=137431:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=145761:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1024_afp=1000:avsq=on:awrs=converge:bd=preordered:drc=off:ins=1:ss=axioms:st=5.0:to=lpo:uwa=interpreted_only:i=131584:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:5_av=off:bs=unit_only:drc=off:fd=preordered:gs=on:lwlo=on:newcnf=on:plsq=on:plsql=on:plsqr=32,1:thi=neg_eq:i=81628:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_3:1_bd=off:fde=none:lwlo=on:i=20528:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:6_bd=off:drc=off:tgt=full:i=26171:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:32_tgt=ground:i=57745:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:128_drc=off:ins=1:sp=const_frequency:tgt=ground:i=11675:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+33_1:4_lwlo=on:s2a=on:tgt=ground:i=41523:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:3_drc=off:fd=off:nwc=5.0:plsq=on:plsql=on:slsq=on:slsql=off:slsqr=17,16:sp=occurrence:i=7301:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_13:991_awrs=decay:awrsf=1:bd=preordered:drc=off:fd=preordered:sp=const_frequency:spb=goal_then_units:uwa=all:i=62964:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:128_aac=none:acc=on:amm=off:atotf=0.1:bd=preordered:drc=off:fd=preordered:fde=none:gs=on:nicw=on:s2a=on:s2at=5.0:slsq=on:sp=const_max:spb=non_intro:tgt=ground:to=lpo:i=87610:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:5_bs=unit_only:drc=off:ins=1:nwc=2.16:rnwc=on:slsq=on:slsqr=13,149:sp=const_min:tgt=ground:to=lpo:uwa=interpreted_only:i=136748:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:rp=on:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=147183:si=on:rawr=on:rtra=on_0");
    // Improves by expected 11.399393780969165 probs costing 1149715 Mi
    // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
    quick.push("dis+1011_1:227_abs=on:amm=off:avsq=on:avsqc=1:avsqr=97,32:awrs=converge:awrsf=256:bsr=unit_only:drc=off:fd=preordered:plsq=on:plsqc=1:plsql=on:plsqr=27942579,963352:sas=z3:slsq=on:slsqc=1:slsql=off:slsqr=307,512:sp=occurrence:ss=axioms:st=3.0:i=4918:si=on:rawr=on:rtra=on_0");
    quick.push("ott+4_1:1_atotf=0.5:bce=on:ins=1:sp=frequency:spb=units:i=189643:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1024_afp=1000:avsq=on:awrs=converge:bd=preordered:drc=off:ins=1:ss=axioms:st=5.0:to=lpo:uwa=interpreted_only:i=131584:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:5_av=off:bs=unit_only:drc=off:fd=preordered:gs=on:lwlo=on:newcnf=on:plsq=on:plsql=on:plsqr=32,1:thi=neg_eq:i=81628:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:6_bd=off:drc=off:tgt=full:i=26171:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:12_drc=off:fd=preordered:tgt=full:i=466188:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=318718:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:32_tgt=ground:i=57745:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_fd=preordered:kws=inv_frequency:tgt=full:i=316573:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_1:1024_bd=off:bs=on:drc=off:kmz=on:kws=precedence:plsq=on:spb=goal:tgt=full:i=93622:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:5_bs=unit_only:drc=off:ins=1:nwc=2.16:rnwc=on:slsq=on:slsqr=13,149:sp=const_min:tgt=ground:to=lpo:uwa=interpreted_only:i=139367:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bd=off:lwlo=on:i=166476:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:rp=on:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=404250:si=on:rawr=on:rtra=on_0");
    // Improves by expected 5.9060816957061695 probs costing 2396870 Mi
    // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
    quick.push("dis+1011_1:227_abs=on:amm=off:avsq=on:avsqc=1:avsqr=97,32:awrs=converge:awrsf=256:bsr=unit_only:drc=off:fd=preordered:plsq=on:plsqc=1:plsql=on:plsqr=27942579,963352:sas=z3:slsq=on:slsqc=1:slsql=off:slsqr=307,512:sp=occurrence:ss=axioms:st=3.0:i=7806:si=on:rawr=on:rtra=on_0");
    quick.push("ott+4_1:1_atotf=0.5:bce=on:ins=1:sp=frequency:spb=units:i=189470:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:12_drc=off:fd=preordered:tgt=full:i=466188:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_fd=preordered:kws=inv_frequency:tgt=full:i=316573:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_1:1024_bd=off:bs=on:drc=off:kmz=on:kws=precedence:plsq=on:spb=goal:tgt=full:i=93622:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:5_bs=unit_only:drc=off:ins=1:nwc=2.16:rnwc=on:slsq=on:slsqr=13,149:sp=const_min:tgt=ground:to=lpo:uwa=interpreted_only:i=149320:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:rp=on:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=404250:si=on:rawr=on:rtra=on_0");
    // Improves by expected 1.3024502930268869 probs costing 1627222 Mi
    // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
    quick.push("ott+4_1:1_atotf=0.5:bce=on:ins=1:sp=frequency:spb=units:i=189470:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:12_drc=off:fd=preordered:tgt=full:i=466188:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:rp=on:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=404250:si=on:rawr=on:rtra=on_0");
    // Improves by expected 0.45225865890697925 probs costing 1059905 Mi
    // Overall score 931.6063932304647 probs on average / budget 7614426 Mi
  } else if (property.category() == Property::Category::FNE || property.category() == Property::Category::FEQ) {
    // problemsFOFUNS.txt
    // Champion singleton-schedule for 100000Mi
    quick.push("dis+1002_1:12_drc=off:fd=preordered:tgt=full:i=99978:si=on:rawr=on:rtra=on_0");
    // Improves by expected 4482.0263626925025 probs costing 99977 Mi
    // Sub-schedule for 50Mi strat cap / 400Mi overall limit
    quick.push("lrs+10_1:1_gsp=on:sd=1:sgt=32:sos=on:ss=axioms:i=13:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_aac=none:bd=off:sac=on:sos=on:spb=units:i=3:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_5:1_br=off:fde=none:nwc=3.0:sd=1:sgt=10:sos=on:ss=axioms:urr=on:i=51:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1024_nm=0:nwc=5.0:ss=axioms:i=13:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_av=off:sos=on:sp=frequency:ss=included:to=lpo:i=15:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:50_awrs=decay:awrsf=128:nwc=10.0:s2pl=no:sp=frequency:ss=axioms:i=39:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:1_lcm=reverse:lma=on:sos=all:spb=goal_then_units:ss=included:urr=on:i=39:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_newcnf=on:sgt=8:sos=on:ss=axioms:to=lpo:urr=on:i=49:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:sos=on:ss=axioms:st=2.0:urr=on:i=33:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ep=R:lcm=predicate:lma=on:sos=all:spb=goal:ss=included:i=12:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:2_br=off:nm=4:ss=included:urr=on:i=7:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:4_av=off:bs=unit_only:bsr=unit_only:ep=RS:s2a=on:sos=on:sp=frequency:to=lpo:i=16:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_br=off:nm=16:sd=2:ss=axioms:st=2.0:urr=on:i=51:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ins=3:sp=reverse_frequency:spb=goal:to=lpo:i=3:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_drc=off:sp=reverse_frequency:spb=goal:to=lpo:i=7:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_fd=preordered:fsd=on:sos=on:thsq=on:thsqc=64:thsqd=32:uwa=ground:i=50:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_nm=2:i=3:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1010_1:1_sd=2:sos=on:sp=occurrence:ss=axioms:urr=on:i=2:si=on:rawr=on:rtra=on_0");
    quick.push("dis-10_3:2_amm=sco:ep=RS:fsr=off:nm=10:sd=2:sos=on:ss=axioms:st=3.0:i=11:si=on:rawr=on:rtra=on_0");
    // Improves by expected 285.78534601289596 probs costing 398 Mi
    // Sub-schedule for 100Mi strat cap / 800Mi overall limit
    quick.push("dis+1010_1:1_bs=on:ep=RS:erd=off:newcnf=on:nwc=10.0:s2a=on:sgt=32:ss=axioms:i=30:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_1:1_erd=off:s2a=on:sac=on:sd=1:sgt=64:sos=on:ss=included:st=3.0:to=lpo:urr=on:i=99:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_2:3_fs=off:fsr=off:nm=0:nwc=5.0:s2a=on:s2agt=32:i=82:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:sos=on:sp=reverse_arity:ss=included:st=2.0:to=lpo:urr=ec_only:i=45:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_ep=RS:nwc=10.0:s2a=on:s2at=1.5:i=50:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_plsq=on:plsqc=1:plsqr=32,1:ss=included:i=95:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_fd=preordered:fsd=on:sos=on:thsq=on:thsqc=64:thsqd=32:uwa=ground:i=99:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_aac=none:abs=on:er=known:fde=none:fsr=off:nwc=5.0:s2a=on:s2at=4.0:sp=const_frequency:to=lpo:urr=ec_only:i=25:si=on:rawr=on:rtra=on_0");
    quick.push("dis+2_3:1_aac=none:abs=on:ep=R:lcm=reverse:nwc=10.0:sos=on:sp=const_frequency:spb=units:urr=ec_only:i=8:si=on:rawr=on:rtra=on_0");
    quick.push("lrs-11_1:1_nm=0:sac=on:sd=4:ss=axioms:st=3.0:i=24:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_afq=1.1:anc=none:bd=off:sd=2:sos=on:ss=axioms:i=92:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_afp=100000:afq=1.4:bd=preordered:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:sd=1:sos=all:sp=const_min:ss=axioms:i=7:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_bd=off:sd=2:sos=all:sp=unary_frequency:ss=axioms:i=87:si=on:rawr=on:rtra=on_0");
    quick.push("ott+4_1:28_av=off:sos=all:i=69:si=on:rawr=on:rtra=on_0");
    // Improves by expected 111.7143459428427 probs costing 798 Mi
    // Sub-schedule for 150Mi strat cap / 1200Mi overall limit
    quick.push("dis+1011_1:1_av=off:er=known:fde=unused:nwc=10.0:slsq=on:slsqc=1:slsqr=4,15:i=107:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:skr=on:ss=axioms:i=56:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_5:1_br=off:fde=none:nwc=3.0:sd=1:sgt=10:sos=on:ss=axioms:urr=on:i=141:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:16_fsr=off:nwc=2.0:i=42:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_ep=RS:sos=on:i=31:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=RST:fs=off:fsr=off:s2a=on:i=68:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:4_amm=off:bce=on:sd=1:sos=on:ss=included:i=84:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:s2a=on:s2agt=8:ss=axioms:st=2.0:urr=on:i=131:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:16_gsp=on:lcm=reverse:sd=2:sp=frequency:spb=goal_then_units:ss=included:i=93:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_br=off:nm=16:sd=2:ss=axioms:st=2.0:urr=on:i=109:si=on:rawr=on:rtra=on_0");
    quick.push("dis+32_1:1_bd=off:nm=4:sos=on:ss=included:i=86:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+4_1:1_fde=unused:sos=on:i=15:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_5:1_drc=off:kws=inv_arity_squared:nwc=5.0:plsq=on:plsqc=1:plsqr=32,1:s2a=on:s2at=2.1:urr=ec_only:i=32:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:32_ep=RS:ss=axioms:st=5.0:i=149:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_ep=R:sd=1:sos=all:ss=axioms:i=66:si=on:rawr=on:rtra=on_0");
    // Improves by expected 98.17648750011675 probs costing 1195 Mi
    // Sub-schedule for 500Mi strat cap / 4000Mi overall limit
    quick.push("ott+10_4:7_awrs=converge:bd=preordered:flr=on:nwc=10.0:sos=on:sp=reverse_frequency:to=lpo:urr=on:i=19:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_ins=1:sd=1:sos=on:ss=axioms:to=lpo:i=341:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_1:1_erd=off:s2a=on:sac=on:sd=1:sgt=64:sos=on:ss=included:st=3.0:to=lpo:urr=on:i=237:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bd=off:drc=off:lcm=reverse:nwc=5.0:sd=1:sgt=16:spb=goal_then_units:ss=axioms:to=lpo:i=10:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_5:1_br=off:fde=none:nwc=3.0:sd=1:sgt=10:sos=on:ss=axioms:urr=on:i=472:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1024_nm=0:nwc=5.0:ss=axioms:i=21:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:1_ep=R:fde=none:lcm=reverse:nwc=5.0:sos=on:i=97:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:sd=2:sos=on:ss=axioms:st=1.5:i=21:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_nwc=3.0:sd=1:spb=goal_then_units:ss=included:to=lpo:i=138:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_newcnf=on:sgt=8:sos=on:ss=axioms:to=lpo:urr=on:i=393:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:sos=on:ss=axioms:st=2.0:urr=on:i=488:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1004_1:1_br=off:fsd=on:urr=ec_only:i=93:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:8_ep=R:nwc=5.0:rnwc=on:sos=on:urr=on:i=23:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_sd=1:sos=on:sp=frequency:ss=included:to=lpo:i=221:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+35_1:2_av=off:bsr=unit_only:flr=on:lcm=predicate:sp=frequency:i=222:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1003_1:128_atotf=0.3:bce=on:newcnf=on:urr=on:i=86:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_aac=none:bs=unit_only:ep=RS:gsp=on:nwc=5.0:rnwc=on:s2a=on:s2at=3.0:slsq=on:slsqc=2:slsqr=1,8:i=79:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:32_awrs=converge:awrsf=32:bd=preordered:drc=off:fd=preordered:flr=on:to=lpo:i=377:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:64_plsq=on:plsqr=32,1:sac=on:sos=all:ss=axioms:st=5.0:i=118:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:4_av=off:bd=off:drc=off:ins=1:nwc=2.0:spb=goal:tgt=full:to=lpo:i=113:si=on:rawr=on:rtra=on_0");
    quick.push("dis+2_3:1_aac=none:abs=on:ep=R:lcm=reverse:nwc=10.0:sos=on:sp=const_frequency:spb=units:urr=ec_only:i=8:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_av=off:gs=on:gsp=on:irw=on:nwc=2.0:sd=2:sos=on:ss=axioms:stl=30:urr=on:i=390:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:16_lma=on:nicw=on:sd=7:sp=const_frequency:ss=axioms:st=5.0:urr=ec_only:i=23:si=on:rawr=on:rtra=on_0");
    // Improves by expected 311.45906569091017 probs costing 4000 Mi
    // Sub-schedule for 1000Mi strat cap / 8000Mi overall limit
    quick.push("dis+1011_1:1_av=off:er=known:fde=unused:nwc=10.0:slsq=on:slsqc=1:slsqr=4,15:i=357:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_abs=on:br=off:urr=ec_only:i=366:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:2_br=off:bs=unit_only:bsr=unit_only:nwc=5.0:s2a=on:s2agt=32:urr=on:i=424:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_aac=none:bd=off:sac=on:sos=on:spb=units:i=753:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:2_aac=none:acc=on:alpa=true:spb=units:i=288:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=1:sos=on:spb=goal_then_units:ss=included:to=lpo:i=1000:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:50_awrs=decay:awrsf=128:nwc=10.0:s2pl=no:sp=frequency:ss=axioms:i=149:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_5:1_bce=on:bd=off:bsr=unit_only:s2a=on:sos=all:sp=reverse_arity:ss=axioms:st=2.0:to=lpo:urr=on:i=35:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_av=off:dr=on:ep=RS:mep=off:newcnf=on:nm=2:nwc=10.0:s2a=on:slsq=on:slsqc=0:slsqr=1,8:i=377:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:fd=off:fde=none:ins=3:sac=on:sos=on:spb=goal:to=lpo:i=300:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_nm=0:nwc=2.0:s2a=on:spb=goal_then_units:to=lpo:i=45:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:8_ep=R:nwc=5.0:rnwc=on:sos=on:urr=on:i=23:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_aac=none:fs=off:fsr=off:i=136:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_amm=off:drc=off:sp=reverse_frequency:spb=goal_then_units:to=lpo:i=91:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:4_drc=off:sos=on:to=lpo:i=102:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_fd=preordered:fsd=on:sos=on:thsq=on:thsqc=64:thsqd=32:uwa=ground:i=234:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:2_er=filter:fde=unused:nwc=3.0:sac=on:sp=frequency:ss=included:to=lpo:i=246:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_aac=none:bs=unit_only:ep=RS:gsp=on:nwc=5.0:rnwc=on:s2a=on:s2at=3.0:slsq=on:slsqc=2:slsqr=1,8:i=290:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:3_av=off:bd=off:bs=on:bsr=on:cond=on:gsp=on:slsq=on:slsqc=1:slsqr=1,4:uwa=all:i=68:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_ep=R:fde=none:fsr=off:slsq=on:slsqc=1:slsql=off:slsqr=1,4:ss=axioms:i=248:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:5_add=large:afp=4000:anc=none:irw=on:lma=on:nm=64:sac=on:sd=3:sos=on:sp=reverse_arity:ss=axioms:st=2.0:stl=30:updr=off:urr=on:i=126:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1010_1:1_sd=2:sos=on:sp=occurrence:ss=axioms:urr=on:i=997:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_4:1_cond=fast:fde=unused:lcm=predicate:nm=4:s2a=on:sd=3:sos=on:ss=axioms:st=2.0:i=139:si=on:rawr=on:rtra=on_0");
    quick.push("ott+4_8:1_acc=on:fsr=off:lcm=reverse:lma=on:sd=2:sos=all:ss=axioms:st=1.5:i=121:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:1_lwlo=on:nwc=10.0:i=92:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_nwc=5.0:sd=4:ss=included:st=5.0:i=43:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_1:1_aac=none:add=large:anc=all_dependent:cond=fast:ep=RST:fsr=off:lma=on:nm=2:sos=on:sp=reverse_arity:stl=30:uhcvi=on:urr=on:i=50:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bd=preordered:drc=off:rp=on:sp=frequency:to=lpo:urr=on:i=9:si=on:rawr=on:rtra=on_0");
    quick.push("dis-10_3:2_amm=sco:ep=RS:fsr=off:nm=10:sd=2:sos=on:ss=axioms:st=3.0:i=915:si=on:rawr=on:rtra=on_0");
    // Improves by expected 163.4230335954961 probs costing 7995 Mi
    // Sub-schedule for 1500Mi strat cap / 12000Mi overall limit
    quick.push("ott+21_1:1_erd=off:s2a=on:sac=on:sd=1:sgt=64:sos=on:ss=included:st=3.0:to=lpo:urr=on:i=437:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_aac=none:lcm=reverse:nwc=10.0:sos=on:ss=axioms:st=3.0:i=206:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:17_bce=on:bsr=unit_only:drc=off:flr=on:gs=on:sp=frequency:spb=units:to=lpo:i=1287:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:sos=on:ss=axioms:st=2.0:urr=on:i=1501:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bd=off:fd=preordered:fde=unused:sfv=off:sos=on:sp=reverse_frequency:spb=goal:to=lpo:i=32:si=on:rawr=on:rtra=on_0");
    quick.push("dis+4_1:64_av=off:bce=on:flr=on:lcm=reverse:sfv=off:sos=all:i=117:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_bd=off:erd=off:plsq=on:plsqr=32,1:sfv=off:sos=all:i=283:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bsr=on:lma=on:sac=on:sos=all:spb=units:to=lpo:i=115:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:16_gsp=on:lcm=reverse:sd=2:sp=frequency:spb=goal_then_units:ss=included:i=93:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_1:16_av=off:fd=off:newcnf=on:nm=10:sims=off:sos=on:i=92:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_fde=unused:nwc=10.0:s2a=on:s2at=3.0:sac=on:i=80:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+22_1:1_amm=sco:fsr=off:gve=force:sos=on:uwa=all:i=251:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_bd=preordered:drc=off:fd=preordered:fsr=off:plsq=on:i=94:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+30_1:3_aac=none:abs=on:avsq=on:avsql=on:avsqr=1,16:er=filter:fde=none:fsr=off:kws=inv_frequency:nwc=5.0:sup=off:i=285:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=1486:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=73:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_aac=none:abs=on:bce=on:bd=off:bsr=unit_only:drc=off:fd=preordered:fsd=on:gve=cautious:lcm=reverse:nm=16:plsq=on:plsqc=1:plsqr=232,15:sfv=off:slsq=on:slsql=off:slsqr=3,2:sos=on:sp=weighted_frequency:i=106:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_ep=R:sd=2:sos=on:ss=axioms:i=1488:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_sd=1:ss=axioms:st=5.0:i=103:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_3:1_acc=model:fsr=off:gsp=on:sd=1:ss=axioms:st=5.0:urr=on:i=376:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=1:sos=all:ss=axioms:i=1345:si=on:rawr=on:rtra=on_0");
    quick.push("ott-3_2:1_acc=on:add=large:anc=none:fde=none:gsp=on:irw=on:nm=0:s2a=on:sd=4:sos=on:ss=axioms:st=1.2:urr=on:i=134:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_av=off:gs=on:gsp=on:irw=on:nwc=2.0:sd=2:sos=on:ss=axioms:stl=30:urr=on:i=1498:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:5_acc=on:afp=1010:fsr=off:gsp=on:nm=10:sac=on:sos=on:sp=unary_first:urr=ec_only:i=177:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_fmbsr=1.2:rp=on:i=82:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_fde=none:sd=2:sos=on:sp=const_max:ss=axioms:i=274:si=on:rawr=on:rtra=on_0");
    // Improves by expected 138.95187684204046 probs costing 11989 Mi
    // Sub-schedule for 5000Mi strat cap / 40000Mi overall limit
    quick.push("lrs+1011_1:5_av=off:awrs=decay:awrsf=97:bce=on:bsr=on:drc=off:flr=on:gs=on:ins=3:lwlo=on:newcnf=on:nm=0:plsq=on:plsqr=4437,256:s2a=on:s2at=4.0:s2pl=no:sims=off:skr=on:slsq=on:slsqc=0:slsqr=31,16:sos=all:sp=frequency:updr=off:i=176:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:32_bd=off:fde=unused:plsq=on:plsqc=2:plsqr=175,8:s2a=on:sp=frequency:spb=goal:ss=included:st=2.0:to=lpo:i=669:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_av=off:sos=on:sp=frequency:ss=included:to=lpo:i=156:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:50_bsr=unit_only:drc=off:fd=preordered:sp=frequency:i=1735:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:ep=RS:lcm=reverse:newcnf=on:s2a=on:s2at=3.0:i=2681:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_lma=on:sac=on:sos=all:spb=goal_then_units:ss=axioms:to=lpo:i=432:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_bsr=unit_only:flr=on:to=lpo:i=440:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=1:sos=on:ss=included:i=3303:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_ss=included:st=2.0:i=503:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sos=on:ss=included:st=1.2:urr=on:i=236:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_3:1_br=off:flr=on:sgt=8:ss=axioms:urr=on:i=128:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_ep=RS:erd=off:sac=on:sos=on:i=2543:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_nm=0:nwc=2.0:s2a=on:spb=goal_then_units:to=lpo:i=45:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_acc=model:bd=off:ins=1:nwc=5.0:sp=reverse_frequency:to=lpo:i=279:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+0_1:1_br=off:drc=off:erd=off:urr=ec_only:i=997:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:16_gsp=on:lcm=reverse:sd=2:sp=frequency:spb=goal_then_units:ss=included:i=121:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_br=off:gsp=on:nm=6:nwc=5.0:urr=on:i=53:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_aac=none:fs=off:fsr=off:i=265:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:5_bsr=on:drc=off:ins=1:nwc=2.8:sp=reverse_frequency:to=lpo:i=84:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_acc=model:avsq=on:bd=off:flr=on:fsd=on:gs=on:newcnf=on:plsq=on:plsql=on:plsqr=1,32:s2a=on:s2at=3.0:sac=on:skr=on:sos=on:sp=occurrence:updr=off:i=162:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_aac=none:bs=unit_only:ep=RS:gsp=on:nwc=5.0:rnwc=on:s2a=on:s2at=3.0:slsq=on:slsqc=2:slsqr=1,8:i=1290:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_fde=unused:nwc=10.0:s2a=on:s2at=3.0:sac=on:i=3040:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:4_abs=on:bsd=on:fsd=on:nwc=3.0:sas=z3:slsq=on:slsqc=2:slsql=off:slsqr=1,8:i=192:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_av=off:bd=off:br=off:erd=off:ins=1:nm=0:nwc=3.0:s2a=on:slsq=on:slsqc=2:slsqr=1,2:urr=on:i=163:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=3643:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:6_bd=off:drc=off:tgt=full:i=729:si=on:rawr=on:rtra=on_0");
    quick.push("dis+20_1:12_aac=none:acc=model:awrs=converge:fd=preordered:fsr=off:nicw=on:nwc=3.0:s2a=on:s2agt=16:spb=goal:to=lpo:i=292:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=73:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:8_av=off:bs=unit_only:drc=off:flr=on:lwlo=on:nwc=10.0:slsq=on:slsqr=1,4:tgt=ground:to=lpo:urr=on:i=1174:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1024_br=off:nwc=3.0:plsq=on:plsqc=2:plsqr=7,4:urr=on:i=348:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+31_1:1_fs=off:fsr=off:kws=precedence:i=772:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_anc=all:br=off:newcnf=on:s2a=on:s2at=2.0:sac=on:sd=1:ss=included:urr=on:i=3380:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1024_av=off:awrs=converge:awrsf=256:bce=on:bsr=on:fde=unused:gs=on:ins=1:nwc=3.0:s2a=on:skr=on:i=388:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_av=off:br=off:bsd=on:drc=off:s2a=on:sos=all:sp=reverse_arity:spb=goal:to=lpo:urr=on:i=198:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:bd=off:lma=on:sfv=off:sos=all:spb=goal_then_units:to=lpo:i=226:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:5_bs=unit_only:drc=off:ins=1:nwc=2.16:rnwc=on:slsq=on:slsqr=13,149:sp=const_min:tgt=ground:to=lpo:uwa=interpreted_only:i=336:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:32_ep=RS:ss=axioms:st=5.0:i=206:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_nwc=5.0:sd=4:ss=included:st=5.0:i=2097:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_av=off:gs=on:gsp=on:irw=on:nwc=2.0:sd=2:sos=on:ss=axioms:stl=30:urr=on:i=4956:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_2:1_add=large:afp=4000:newcnf=on:sd=1:sos=on:sp=const_min:ss=axioms:i=322:si=on:rawr=on:rtra=on_0");
    quick.push("dis+3_1:64_av=off:cond=on:lcm=reverse:nwc=3.0:sos=on:updr=off:i=1004:si=on:rawr=on:rtra=on_0");
    // Improves by expected 273.5128705685998 probs costing 39996 Mi
    // Sub-schedule for 10000Mi strat cap / 80000Mi overall limit
    quick.push("lrs+1011_1:5_av=off:awrs=decay:awrsf=97:bce=on:bsr=on:drc=off:flr=on:gs=on:ins=3:lwlo=on:newcnf=on:nm=0:plsq=on:plsqr=4437,256:s2a=on:s2at=4.0:s2pl=no:sims=off:skr=on:slsq=on:slsqc=0:slsqr=31,16:sos=all:sp=frequency:updr=off:i=654:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_aac=none:bce=on:nicw=on:nm=0:plsq=on:plsql=on:sac=on:sos=on:sp=frequency:spb=units:to=lpo:i=455:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_av=off:er=known:fde=unused:nwc=10.0:slsq=on:slsqc=1:slsqr=4,15:i=98:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_cond=on:erd=off:fsd=on:fsdmm=2:gs=on:newcnf=on:nwc=2.0:s2a=on:sims=off:sp=reverse_arity:ss=axioms:i=186:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_gsp=on:sd=1:sgt=32:sos=on:ss=axioms:i=473:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:16_fsd=on:nicw=on:ss=included:i=433:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_abs=on:br=off:urr=ec_only:i=453:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:7_av=off:awrs=converge:awrsf=40:br=off:bsd=on:cond=on:drc=off:nwc=3.0:plsq=on:plsqc=1:s2a=on:s2agt=16:to=lpo:urr=on:i=802:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_ins=1:sd=1:sos=on:ss=axioms:to=lpo:i=848:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_av=off:nwc=5.0:s2a=on:s2at=2.2:spb=goal_then_units:to=lpo:i=452:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_atotf=0.1:lcm=predicate:nwc=5.0:rnwc=on:s2a=on:s2at=2.0:sac=on:sos=on:spb=goal_then_units:urr=on:i=644:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:128_aac=none:avsq=on:avsqc=2:avsql=on:avsqr=1,16:awrs=converge:bs=on:nm=0:plsq=on:plsqc=1:plsqr=65,12:sos=on:spb=goal_then_units:to=lpo:urr=on:i=855:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_4:1_acc=on:alpa=true:awrs=converge:bsr=unit_only:fsd=on:gs=on:gsaa=from_current:nicw=on:s2a=on:s2at=2.0:sac=on:slsq=on:slsqc=2:slsqr=11,120:sos=all:sp=weighted_frequency:spb=goal_then_units:urr=on:i=3379:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_5:1_br=off:fde=none:nwc=3.0:sd=1:sgt=10:sos=on:ss=axioms:urr=on:i=1340:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_2388710:563463_bce=on:ep=RS:erd=off:fs=off:fsr=off:sp=frequency:i=1024:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=4:sos=on:spb=goal:ss=axioms:st=3.7:to=lpo:urr=on:i=480:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:1_ep=R:fde=none:lcm=reverse:nwc=5.0:sos=on:i=543:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:ep=RS:lcm=reverse:newcnf=on:s2a=on:s2at=3.0:i=2849:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_newcnf=on:sgt=8:sos=on:ss=axioms:to=lpo:urr=on:i=670:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_2:3_fs=off:fsr=off:nm=0:nwc=5.0:s2a=on:s2agt=32:i=918:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_nwc=2.0:ss=axioms:st=1.3:urr=on:i=2016:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_av=off:bce=on:bs=on:ep=RST:gsp=on:nm=0:s2a=on:ss=included:i=124:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_av=off:br=off:erd=off:ins=1:nm=3:nwc=3.0:s2a=on:urr=on:i=439:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_5:1_abs=on:ep=RST:fde=unused:gsp=on:ins=1:nwc=10.0:s2a=on:s2at=1.5:sas=z3:sp=reverse_frequency:i=778:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_bsr=unit_only:cond=on:nm=16:sd=1:sp=frequency:ss=included:i=105:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:10_av=off:awrs=decay:bce=on:bd=off:bsd=on:nwc=2.0:i=1536:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_atotf=0.3:avsq=on:avsqr=55,124:cond=on:nm=3:plsq=on:plsqc=1:plsql=on:plsqr=32,1:i=167:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_3:1_abs=on:ep=RST:newcnf=on:nm=2:sas=z3:sd=1:sos=all:ss=included:to=lpo:i=4507:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1004_1:1_br=off:fsd=on:urr=ec_only:i=93:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:fd=off:fde=none:ins=3:sac=on:sos=on:spb=goal:to=lpo:i=529:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1024_av=off:br=off:s2at=3.0:slsq=on:slsqc=2:slsql=off:slsqr=1,8:urr=ec_only:i=1275:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:gs=on:newcnf=on:nm=2:plsq=on:plsqr=32,1:sd=1:sos=all:ss=included:st=3.0:i=507:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:28_av=off:nwc=5.0:s2a=on:s2at=3.0:i=354:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_fde=none:flr=on:s2a=on:i=210:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:16_gsp=on:lcm=reverse:sd=2:sp=frequency:spb=goal_then_units:ss=included:i=93:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bsr=on:erd=off:nwc=5.0:plsq=on:plsqc=1:plsqr=107,4:s2a=on:s2at=1.5:sas=z3:sp=reverse_frequency:spb=units:updr=off:i=1114:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_newcnf=on:nwc=5.0:i=189:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=R:gsp=on:nm=0:sos=on:spb=units:ss=included:i=351:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1004_1:1_av=off:bd=off:sos=all:i=144:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1003_1:1_bce=on:bd=preordered:drc=off:fd=preordered:to=lpo:uwa=ground:i=318:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_aac=none:er=known:lcm=predicate:nwc=3.0:sp=frequency:i=471:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:4_drc=off:sos=on:to=lpo:i=689:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:16_etr=on:fsd=on:fsr=off:ins=1:plsq=on:plsqr=32,1:sac=on:sp=frequency:spb=goal:ss=axioms:st=2.0:to=lpo:i=451:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:2_acc=on:avsq=on:avsqc=2:avsqr=1,16:awrs=converge:plsq=on:plsqc=1:plsqr=15,8:i=125:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_acc=model:avsq=on:bd=off:flr=on:fsd=on:gs=on:newcnf=on:plsq=on:plsql=on:plsqr=1,32:s2a=on:s2at=3.0:sac=on:skr=on:sos=on:sp=occurrence:updr=off:i=496:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1024_drc=off:ins=1:to=lpo:i=370:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:64_av=off:bd=off:gsp=on:plsq=on:sos=on:i=134:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:3_aac=none:anc=all_dependent:bsr=on:fsr=off:nwc=1.5:sos=on:i=401:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_aac=none:bs=unit_only:ep=RS:gsp=on:nwc=5.0:rnwc=on:s2a=on:s2at=3.0:slsq=on:slsqc=2:slsqr=1,8:i=1879:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1024_br=off:bs=unit_only:ep=RS:flr=on:fsr=off:lcm=reverse:slsq=on:sos=all:sp=frequency:urr=on:i=392:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:32_awrs=converge:awrsf=32:bd=preordered:drc=off:fd=preordered:flr=on:to=lpo:i=3473:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_av=off:bce=on:bs=on:ep=RST:gsp=on:nm=0:ss=included:i=131:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:64_plsq=on:plsqr=32,1:sac=on:sos=all:ss=axioms:st=5.0:i=154:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ev=cautious:sas=z3:tgt=full:i=668:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:4_av=off:bd=off:drc=off:ins=1:nwc=2.0:spb=goal:tgt=full:to=lpo:i=254:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bd=off:canc=force:ev=cautious:nwc=5.0:i=1452:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_bd=preordered:drc=off:fde=unused:slsq=on:slsqr=10,31:sp=const_min:tgt=ground:to=lpo:urr=ec_only:i=2772:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:512_drc=off:fd=preordered:ins=2:kws=precedence:s2a=on:sp=unary_first:spb=intro:tgt=ground:i=3180:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_aac=none:anc=all:bs=on:erd=off:etr=on:flr=on:gsp=on:lcm=reverse:nm=5:nwc=3.0:sac=on:sfv=off:skr=on:sp=reverse_arity:urr=on:uwa=interpreted_only:i=1043:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_fd=preordered:tgt=ground:i=561:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_2:1_av=off:bsd=on:fd=off:nm=0:nwc=2.0:spb=goal:to=lpo:urr=on:i=604:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:16_br=off:fde=none:ins=1:nwc=3.0:sos=on:ss=axioms:urr=on:i=234:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:3_av=off:bd=off:bs=on:bsr=on:cond=on:gsp=on:slsq=on:slsqc=1:slsqr=1,4:uwa=all:i=109:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_13:991_awrs=decay:awrsf=1:bd=preordered:drc=off:fd=preordered:sp=const_frequency:spb=goal_then_units:uwa=all:i=360:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1003_1:1_bce=on:fs=off:fsr=off:gs=on:newcnf=on:plsq=on:plsqr=32,1:skr=on:sos=on:sp=frequency:spb=units:i=660:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_3:29_av=off:awrs=decay:awrsf=32:bce=on:drc=off:fde=unused:gsp=on:irw=on:nwc=2.0:spb=goal_then_units:updr=off:urr=ec_only:i=982:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_39044:804583_anc=all:avsq=on:avsqr=302,909:awrs=decay:awrsf=20:bd=off:bsr=on:cond=on:gsp=on:nm=0:nwc=2.0:plsq=on:plsqr=9,13:s2a=on:s2agt=16:sac=on:thsq=on:thsqc=32:thsqd=32:thsql=off:to=lpo:updr=off:uwa=all:i=1174:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1003_1:128_avsq=on:bce=on:newcnf=on:urr=on:i=91:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_ep=R:fde=none:fsr=off:slsq=on:slsqc=1:slsql=off:slsqr=1,4:ss=axioms:i=248:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_fde=unused:fmbas=predicate:gsp=on:newcnf=on:nm=0:i=1985:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_sd=2:sos=on:ss=axioms:st=5.0:i=555:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_2:1_add=off:amm=sco:anc=none:br=off:sd=1:sos=all:ss=axioms:st=1.5:updr=off:urr=on:i=484:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:5_add=large:afp=4000:anc=none:irw=on:lma=on:nm=64:sac=on:sd=3:sos=on:sp=reverse_arity:ss=axioms:st=2.0:stl=30:updr=off:urr=on:i=362:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_4:1_br=off:fde=unused:nm=16:s2a=on:sd=3:sp=frequency:ss=axioms:urr=on:i=5368:si=on:rawr=on:rtra=on_0");
    quick.push("ott+4_8:1_acc=on:fsr=off:lcm=reverse:lma=on:sd=2:sos=all:ss=axioms:st=1.5:i=121:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=off:irw=on:lma=on:sd=2:sos=all:sp=const_min:ss=axioms:stl=40:i=256:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_afq=1.1:anc=none:bd=off:sd=2:sos=on:ss=axioms:i=6912:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_3:2_br=off:sas=z3:sd=3:sos=all:ss=axioms:st=3.0:urr=on:i=525:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_amm=off:cond=on:sd=3:sos=on:ss=axioms:st=1.5:i=600:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_av=off:ep=RSTC:rp=on:sos=on:i=723:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_bd=off:sd=2:sos=on:ss=axioms:st=2.0:i=4344:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:gs=on:sd=2:sos=all:ss=axioms:st=2.0:i=873:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:128_nm=2:i=973:si=on:rawr=on:rtra=on_0");
    // Improves by expected 174.23740181977212 probs costing 79961 Mi
    // Sub-schedule for 15000Mi strat cap / 120000Mi overall limit
    quick.push("dis+1011_1:1_av=off:er=known:fde=unused:nwc=10.0:slsq=on:slsqc=1:slsqr=4,15:i=98:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1024_aac=none:acc=model:anc=all_dependent:avsq=on:avsqc=1:avsqr=9,4:drc=off:fd=preordered:sac=on:urr=ec_only:i=3342:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=1:sos=on:spb=goal_then_units:ss=included:to=lpo:i=3417:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:64_fsd=on:nwc=2.0:ss=included:st=3.0:i=446:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_2388710:563463_bce=on:ep=RS:erd=off:fs=off:fsr=off:sp=frequency:i=301:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=4:sos=on:spb=goal:ss=axioms:st=3.7:to=lpo:urr=on:i=480:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:7_sos=on:i=1851:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_5:1_bce=on:bd=off:bsr=unit_only:s2a=on:sos=all:sp=reverse_arity:ss=axioms:st=2.0:to=lpo:urr=on:i=598:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_br=off:fd=off:fde=unused:s2a=on:sd=2:sos=all:ss=axioms:st=2.0:to=lpo:urr=on:i=2282:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:sos=on:ss=axioms:st=2.0:urr=on:i=2179:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:7_awrs=converge:bd=preordered:fsr=off:ins=1:s2a=on:sos=on:i=595:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:sos=on:sp=reverse_arity:ss=included:st=2.0:to=lpo:urr=ec_only:i=776:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bce=on:ep=RST:gsp=on:sd=1:sos=on:ss=axioms:urr=on:i=138:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_aac=none:avsq=on:avsqc=1:bd=off:newcnf=on:nm=4:nwc=5.0:s2a=on:sac=on:i=1679:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_10:13_abs=on:amm=off:anc=none:avsq=on:avsqc=1:avsqr=12,23:bsr=on:cond=on:drc=off:fd=preordered:fde=none:flr=on:fsr=off:gs=on:gsaa=full_model:gsem=off:ins=3:lcm=reverse:nwc=5.0:sas=z3:sims=off:skr=on:sos=on:sp=frequency:spb=units:to=lpo:updr=off:urr=on:i=774:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:ep=R:erd=off:gsp=on:slsq=on:slsqc=0:slsqr=1,1:sp=frequency:spb=goal_then_units:to=lpo:i=936:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_atotf=0.3:avsq=on:avsqr=55,124:cond=on:nm=3:plsq=on:plsqc=1:plsql=on:plsqr=32,1:i=167:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1024_awrs=converge:s2a=on:s2at=3.0:ss=included:st=1.5:urr=on:i=557:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_av=off:dr=on:ep=RS:mep=off:newcnf=on:nm=2:nwc=10.0:s2a=on:slsq=on:slsqc=0:slsqr=1,8:i=258:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:2_abs=on:avsq=on:avsqc=2:bce=on:bsr=unit_only:cond=fast:ep=RS:erd=off:newcnf=on:s2a=on:urr=ec_only:i=941:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_2:1_abs=on:fde=none:lcm=reverse:nwc=2.0:plsq=on:plsqc=1:plsql=on:plsqr=4095,256:s2a=on:sac=on:sp=reverse_arity:i=2311:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_ep=RS:erd=off:sac=on:sos=on:i=190:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_sd=1:sos=on:sp=frequency:ss=included:to=lpo:i=319:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_amm=off:br=off:nwc=5.0:sfv=off:sos=all:ss=axioms:to=lpo:urr=ec_only:i=305:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_45163:73544_aac=none:abs=on:add=large:afr=on:alpa=false:amm=off:anc=none:avsq=on:avsqr=57,253:bs=on:bsr=unit_only:cond=fast:ep=R:fde=unused:gsp=on:mep=off:nwc=4.0:skr=on:slsq=on:slsqc=2:slsql=off:slsqr=59173,778640:sp=occurrence:updr=off:i=125:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=R:gsp=on:nm=0:sos=on:spb=units:ss=included:i=229:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bs=unit_only:drc=off:fd=preordered:foolp=on:nwc=5.0:plsq=on:plsql=on:s2a=on:s2at=3.0:sp=frequency:to=lpo:uwa=interpreted_only:i=835:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_afr=on:fde=none:newcnf=on:nwc=3.0:sas=z3:sos=all:spb=goal:ss=axioms:st=2.0:to=lpo:i=1618:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_amm=off:br=off:bs=on:etr=on:fsd=on:newcnf=on:plsq=on:plsqc=2:plsql=on:s2a=on:s2at=3.0:sac=on:sd=2:sfv=off:sos=all:sp=frequency:ss=axioms:urr=on:i=592:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_fd=preordered:fsd=on:sos=on:thsq=on:thsqc=64:thsqd=32:uwa=ground:i=511:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_av=off:bce=on:bs=on:ep=RST:gsp=on:nm=0:ss=included:i=131:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:64_plsq=on:plsqr=32,1:sac=on:sos=all:ss=axioms:st=5.0:i=154:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_bd=preordered:drc=off:fd=preordered:fsr=off:plsq=on:i=1003:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_av=off:bd=off:br=off:erd=off:ins=1:nm=0:nwc=3.0:s2a=on:slsq=on:slsqc=2:slsqr=1,2:urr=on:i=1141:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_26459:191296_av=off:awrs=converge:awrsf=30:bd=preordered:bs=unit_only:drc=off:etr=on:flr=on:lwlo=on:nwc=5.0:plsq=on:plsqc=1:plsql=on:plsqr=1,32:skr=on:slsq=on:slsqr=18,107:sp=const_min:tgt=ground:to=lpo:urr=ec_only:i=8110:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=12213:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1024_av=off:erd=off:fde=none:s2agt=32:slsq=on:slsqc=1:i=2082:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1024_br=off:nwc=3.0:plsq=on:plsqc=2:plsqr=7,4:urr=on:i=287:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:nm=5:plsq=on:plsqc=1:plsqr=32,1:urr=on:i=820:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+22_1:1_av=off:bsr=unit_only:nwc=3.0:plsq=on:plsqc=1:plsql=on:plsqr=3695814,127453:s2a=on:s2at=2.0:slsq=on:slsqc=1:slsqr=4,3:tgt=full:i=980:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:4_av=off:bd=off:br=off:fsr=off:plsq=on:plsqr=20,11:s2a=on:urr=ec_only:i=3380:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_2:1_av=off:fsr=off:lcm=predicate:nm=2:nwc=3.0:plsq=on:s2a=on:s2agt=47:slsq=on:slsqc=1:slsqr=1,4:sp=reverse_arity:spb=goal_then_units:i=3898:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1024_br=off:gsp=on:nm=4:sos=all:urr=on:i=884:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_av=off:br=off:bsd=on:drc=off:s2a=on:sos=all:sp=reverse_arity:spb=goal:to=lpo:urr=on:i=198:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_ep=R:fde=none:fsr=off:slsq=on:slsqc=1:slsql=off:slsqr=1,4:ss=axioms:i=169:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_br=off:bsr=on:fsr=off:nwc=2.0:s2a=on:s2agt=12:s2at=5.0:urr=on:i=2851:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_fde=unused:fmbas=predicate:gsp=on:newcnf=on:nm=0:i=870:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:5_bs=unit_only:drc=off:ins=1:nwc=2.16:rnwc=on:slsq=on:slsqr=13,149:sp=const_min:tgt=ground:to=lpo:uwa=interpreted_only:i=615:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1_av=off:fde=none:fmbsr=1.6:updr=off:i=914:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:sp=occurrence:i=581:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_sd=2:sos=on:ss=axioms:st=5.0:i=1559:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_3:1_av=off:bd=off:cond=fast:sd=2:sos=all:ss=axioms:i=2142:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_2:1_av=off:newcnf=on:nwc=3.0:sos=all:i=1626:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1_4:1_lcm=predicate:nwc=3.0:sac=on:sd=1:sos=on:ss=axioms:i=870:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1010_1:1_sd=2:sos=on:sp=occurrence:ss=axioms:urr=on:i=7249:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_nm=32:sas=z3:sd=1:sos=on:ss=axioms:i=996:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_4:1_br=off:gsp=on:nwc=2.0:s2a=on:sac=on:ss=axioms:urr=on:i=8959:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_3:1_aac=none:afp=100000:irw=on:nwc=5.0:i=1163:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_sd=2:ss=axioms:st=1.5:i=1204:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=off:irw=on:lma=on:sd=2:sos=all:sp=const_min:ss=axioms:stl=40:i=8197:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_2:3_av=off:lcm=predicate:lma=on:sd=2:sos=all:ss=axioms:i=1156:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_1:1_av=off:lcm=reverse:lma=on:sd=2:sos=all:ss=axioms:st=1.5:i=1751:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_ep=R:sd=1:sos=all:ss=axioms:i=2277:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_anc=all:ep=RST:fde=unused:fsr=off:gsp=on:nm=16:sd=2:sos=on:ss=axioms:st=5.0:i=4113:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:4_afp=10010:amm=off:anc=none:awrs=decay:awrsf=50:ep=RSTC:fde=unused:lma=on:nm=16:nwc=5.0:s2a=on:sp=frequency:urr=ec_only:i=1325:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:nwc=2.0:sd=4:ss=axioms:st=3.0:i=2828:si=on:rawr=on:rtra=on_0");
    quick.push("dis-10_3:2_amm=sco:ep=RS:fsr=off:nm=10:sd=2:sos=on:ss=axioms:st=3.0:i=1473:si=on:rawr=on:rtra=on_0");
    // Improves by expected 121.55099555421971 probs costing 119862 Mi
    // Sub-schedule for 50000Mi strat cap / 400000Mi overall limit
    quick.push("lrs+10_1:1_gsp=on:sd=1:sgt=32:sos=on:ss=axioms:i=473:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_ins=1:sd=1:sos=on:ss=axioms:to=lpo:i=848:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:2_br=off:bs=unit_only:bsr=unit_only:nwc=5.0:s2a=on:s2agt=32:urr=on:i=1750:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_s2a=on:s2agt=10:sgt=8:ss=axioms:i=2236:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_aac=none:bd=off:sac=on:sos=on:spb=units:i=7911:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:28_drc=off:fd=preordered:fsr=off:sp=frequency:to=lpo:i=2536:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_2:217_avsq=on:avsql=on:avsqr=5,12:awrs=decay:awrsf=3:bs=on:drc=off:nwc=3.0:ss=axioms:st=2.0:i=5300:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_2388710:563463_bce=on:ep=RS:erd=off:fs=off:fsr=off:sp=frequency:i=301:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_nwc=2.0:spb=goal_then_units:ss=axioms:st=5.0:i=3178:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=4:sos=on:spb=goal:ss=axioms:st=3.7:to=lpo:urr=on:i=480:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1024_av=off:bs=on:drc=off:flr=on:sp=frequency:to=lpo:i=510:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:bsr=unit_only:plsq=on:plsqc=1:plsql=on:s2a=on:s2at=1.5:sd=2:sos=all:ss=axioms:i=3456:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+4_1:1_flr=on:s2a=on:s2at=3.0:s2pl=on:sd=1:sos=on:ss=included:i=721:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:sos=on:sp=reverse_arity:ss=included:st=2.0:to=lpo:urr=ec_only:i=776:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_ep=RS:newcnf=on:sac=on:urr=ec_only:i=3054:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_aac=none:avsq=on:avsqc=1:bd=off:newcnf=on:nm=4:nwc=5.0:s2a=on:sac=on:i=1679:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_10:13_abs=on:amm=off:anc=none:avsq=on:avsqc=1:avsqr=12,23:bsr=on:cond=on:drc=off:fd=preordered:fde=none:flr=on:fsr=off:gs=on:gsaa=full_model:gsem=off:ins=3:lcm=reverse:nwc=5.0:sas=z3:sims=off:skr=on:sos=on:sp=frequency:spb=units:to=lpo:updr=off:urr=on:i=774:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_atotf=0.3:avsq=on:avsqr=55,124:cond=on:nm=3:plsq=on:plsqc=1:plsql=on:plsqr=32,1:i=167:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_3:1_abs=on:ep=RST:newcnf=on:nm=2:sas=z3:sd=1:sos=all:ss=included:to=lpo:i=28947:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1004_1:1_br=off:fsd=on:urr=ec_only:i=1542:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1024_awrs=converge:s2a=on:s2at=3.0:ss=included:st=1.5:urr=on:i=557:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_av=off:dr=on:ep=RS:mep=off:newcnf=on:nm=2:nwc=10.0:s2a=on:slsq=on:slsqc=0:slsqr=1,8:i=212:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:fd=off:fde=none:ins=3:sac=on:sos=on:spb=goal:to=lpo:i=529:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:2_abs=on:avsq=on:avsqc=2:bce=on:bsr=unit_only:cond=fast:ep=RS:erd=off:newcnf=on:s2a=on:urr=ec_only:i=2058:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1024_av=off:br=off:s2at=3.0:slsq=on:slsqc=2:slsql=off:slsqr=1,8:urr=ec_only:i=3415:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:gs=on:newcnf=on:nm=2:plsq=on:plsqr=32,1:sd=1:sos=all:ss=included:st=3.0:i=906:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_1:1_flr=on:lcm=reverse:nwc=3.0:rnwc=on:sos=on:sp=frequency:spb=goal:i=2132:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ss=axioms:st=3.0:i=1889:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:ep=RSTC:plsq=on:plsqc=1:plsqr=32,1:urr=on:i=46784:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bsr=on:lma=on:sac=on:sos=all:spb=units:to=lpo:i=376:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_4:7_afr=on:awrs=decay:awrsf=8:bce=on:cond=on:flr=on:newcnf=on:plsq=on:plsql=on:plsqr=1,2:sas=z3:skr=on:slsq=on:slsqc=0:slsql=off:slsqr=1,8:sp=frequency:ss=axioms:st=1.2:i=759:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+0_1:1_br=off:drc=off:erd=off:urr=ec_only:i=946:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:128_sd=2:sos=on:ss=axioms:st=3.0:i=347:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_amm=off:br=off:nwc=5.0:sfv=off:sos=all:ss=axioms:to=lpo:urr=ec_only:i=305:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_45163:73544_aac=none:abs=on:add=large:afr=on:alpa=false:amm=off:anc=none:avsq=on:avsqr=57,253:bs=on:bsr=unit_only:cond=fast:ep=R:fde=unused:gsp=on:mep=off:nwc=4.0:skr=on:slsq=on:slsqc=2:slsql=off:slsqr=59173,778640:sp=occurrence:updr=off:i=4772:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=R:gsp=on:nm=0:sos=on:spb=units:ss=included:i=2058:si=on:rawr=on:rtra=on_0");
    quick.push("dis+4_1:1_bd=off:br=off:bsd=on:ins=1:nwc=3.0:s2a=on:s2agt=16:urr=on:i=2519:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_s2a=on:s2agt=16:sd=1:sos=on:ss=included:urr=on:i=4496:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bs=unit_only:drc=off:fd=preordered:foolp=on:nwc=5.0:plsq=on:plsql=on:s2a=on:s2at=3.0:sp=frequency:to=lpo:uwa=interpreted_only:i=835:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=5736:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+32_1:1_ep=R:flr=on:gsp=on:nm=2:s2a=on:s2at=2.0:sas=z3:sd=4:slsq=on:slsqc=2:slsqr=15,16:sos=all:ss=axioms:st=1.5:i=1429:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+34_1:128_asg=cautious:av=off:bs=on:drc=off:fde=unused:fsd=on:fsr=off:gs=on:gve=force:ins=2:inw=on:lma=on:newcnf=on:nm=4:nwc=8.95568:rnwc=on:s2a=on:s2at=1.3:sfv=off:sims=off:skr=on:sos=on:spb=goal:tac=rule:tha=off:thsq=on:thsqc=36:thsqd=16:thsqr=2,47:to=lpo:uace=off:updr=off:i=1818:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_fd=preordered:fsd=on:sos=on:thsq=on:thsqc=64:thsqd=32:uwa=ground:i=511:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:128_av=off:awrs=converge:awrsf=64:irw=on:lcm=reverse:nwc=10.0:sos=on:spb=units:thsq=on:thsqc=32:thsqr=1,2:i=1675:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_3:1_nm=0:s2a=on:s2at=2.0:spb=goal:to=lpo:urr=on:i=284:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_aac=none:bs=unit_only:ep=RS:gsp=on:nwc=5.0:rnwc=on:s2a=on:s2at=3.0:slsq=on:slsqc=2:slsqr=1,8:i=789:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:3_br=off:nwc=2.0:s2a=on:s2agt=64:slsq=on:slsqc=1:slsqr=1,2:urr=on:i=16007:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_av=off:bce=on:bs=on:ep=RST:gsp=on:nm=0:ss=included:i=131:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_awrs=converge:drc=off:kws=inv_frequency:tgt=full:i=39574:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_3:1_av=off:br=off:bsd=on:bsr=on:etr=on:fsd=on:gsp=on:kws=precedence:nwc=10.0:plsq=on:plsqr=2,61:s2at=3.0:slsq=on:slsqc=2:slsqr=1,2:spb=units:tgt=ground:thsq=on:thsqc=16:thsqd=1:updr=off:urr=on:i=1437:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_aac=none:er=known:nwc=3.0:i=331:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bd=off:canc=force:ev=cautious:nwc=5.0:i=646:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:12_drc=off:fd=preordered:tgt=full:i=2222:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=783:si=on:rawr=on:rtra=on_0");
    quick.push("dis+2_1:32_av=off:bce=on:bsr=unit_only:er=filter:fsr=off:gsp=on:newcnf=on:nwc=5.0:s2a=on:s2agt=8:s2at=1.3:sp=unary_first:spb=goal_then_units:thsq=on:thsqc=4:thsqd=32:urr=on:uwa=one_side_constant:i=1606:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:64_bd=preordered:drc=off:s2a=on:spb=goal:tgt=ground:to=lpo:i=11175:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bsr=unit_only:cond=on:flr=on:newcnf=on:nwc=10.0:sas=z3:to=lpo:i=2901:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_anc=all:br=off:newcnf=on:s2a=on:s2at=2.0:sac=on:sd=1:ss=included:urr=on:i=9160:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_2:1_av=off:fsr=off:lcm=predicate:nm=2:nwc=3.0:plsq=on:s2a=on:s2agt=47:slsq=on:slsqc=1:slsqr=1,4:sp=reverse_arity:spb=goal_then_units:i=4289:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1024_av=off:awrs=converge:awrsf=256:bce=on:bsr=on:fde=unused:gs=on:ins=1:nwc=3.0:s2a=on:skr=on:i=388:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bce=on:gs=on:newcnf=on:plsq=on:plsqc=1:plsqr=32,1:skr=on:spb=goal_then_units:urr=ec_only:i=3873:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_5:1_norm_ineq=on:sas=z3:sos=all:ss=axioms:tha=off:i=1359:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_av=off:br=off:bsd=on:drc=off:s2a=on:sos=all:sp=reverse_arity:spb=goal:to=lpo:urr=on:i=2019:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_3:29_av=off:awrs=decay:awrsf=32:bce=on:drc=off:fde=unused:gsp=on:irw=on:nwc=2.0:spb=goal_then_units:updr=off:urr=ec_only:i=2342:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_aac=none:abs=on:add=off:ep=RS:flr=on:fsr=off:lcm=reverse:lma=on:nicw=on:nwc=3.0:sos=all:i=1480:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_39044:804583_anc=all:avsq=on:avsqr=302,909:awrs=decay:awrsf=20:bd=off:bsr=on:cond=on:gsp=on:nm=0:nwc=2.0:plsq=on:plsqr=9,13:s2a=on:s2agt=16:sac=on:thsq=on:thsqc=32:thsqd=32:thsql=off:to=lpo:updr=off:uwa=all:i=575:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_ep=R:fde=none:fsr=off:slsq=on:slsqc=1:slsql=off:slsqr=1,4:ss=axioms:i=248:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_fde=unused:fmbas=predicate:gsp=on:newcnf=on:nm=0:i=1985:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+34_1:1024_av=off:awrs=converge:awrsf=230:bd=off:lma=on:nwc=5.0:s2pl=no:sos=on:tgt=ground:to=lpo:i=1407:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_5:1_acc=model:br=off:nicw=on:s2a=on:ss=axioms:urr=on:i=3171:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sos=all:ss=axioms:st=5.0:i=22148:si=on:rawr=on:rtra=on_0");
    quick.push("lrs-11_1:1_gsp=on:lma=on:nm=6:sd=3:sos=all:sp=reverse_arity:ss=axioms:st=1.2:stl=30:urr=on:i=6308:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_ep=R:sd=2:sos=on:ss=axioms:i=1531:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_sd=1:sos=on:ss=included:i=1723:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:3_anc=none:bd=off:nicw=on:nm=16:sas=z3:sd=2:ss=axioms:st=1.5:i=2462:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:16_awrs=decay:awrsf=260:bsr=on:er=known:gsp=on:newcnf=on:nwc=3.0:s2a=on:sas=z3:sd=4:ss=axioms:i=4063:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_nm=32:sas=z3:sd=1:sos=on:ss=axioms:i=996:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_add=large:afp=100000:afq=2.0:amm=off:anc=none:cond=fast:fde=none:gs=on:gsem=off:lma=on:newcnf=on:nm=64:sos=on:sp=reverse_arity:ss=axioms:i=1868:si=on:rawr=on:rtra=on_0");
    quick.push("ott-3_2:1_acc=on:add=large:anc=none:fde=none:gsp=on:irw=on:nm=0:s2a=on:sd=4:sos=on:ss=axioms:st=1.2:urr=on:i=11674:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_2:3_av=off:lcm=predicate:lma=on:sd=2:sos=all:ss=axioms:i=2634:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_av=off:gsp=on:lcm=predicate:newcnf=on:nm=2:sd=3:sos=on:ss=axioms:i=8552:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_nwc=5.0:sd=4:ss=included:st=5.0:i=21991:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1010_1:3_av=off:fsr=off:gs=on:newcnf=on:nm=2:nwc=2.0:urr=on:i=2613:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_fde=unused:lwlo=on:nwc=5.0:i=3621:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_1:1_aac=none:add=large:anc=all_dependent:cond=fast:ep=RST:fsr=off:lma=on:nm=2:sos=on:sp=reverse_arity:stl=30:uhcvi=on:urr=on:i=1265:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_add=large:afq=1.4:bd=off:newcnf=on:nm=32:sos=all:ss=included:urr=on:i=4091:si=on:rawr=on:rtra=on_0");
    quick.push("lrs-11_1:1_sd=4:sos=on:ss=axioms:st=3.0:i=1960:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_bd=off:sd=2:sos=all:sp=unary_frequency:ss=axioms:i=197:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_3:2_br=off:sas=z3:sd=3:sos=all:ss=axioms:st=3.0:urr=on:i=5217:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_amm=off:cond=on:sd=3:sos=on:ss=axioms:st=1.5:i=1253:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_1:1_av=off:lcm=reverse:lma=on:sd=2:sos=all:ss=axioms:st=1.5:i=7229:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_av=off:gs=on:gsp=on:irw=on:nwc=2.0:sd=2:sos=on:ss=axioms:stl=30:urr=on:i=7809:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_8:1_aac=none:anc=all_dependent:lwlo=on:nm=2:nwc=10.0:sac=on:sos=all:i=1624:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_amm=off:br=off:nwc=5.0:rp=on:sfv=off:sos=all:ss=axioms:to=lpo:urr=ec_only:i=520:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_av=off:ep=RSTC:rp=on:sos=on:i=713:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_fde=none:sd=2:sos=on:sp=const_max:ss=axioms:i=2842:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_bd=off:sd=2:sos=on:ss=axioms:st=2.0:i=5471:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1003_1:1024_add=large:afr=on:cond=fast:fsr=off:gs=on:sos=on:sp=reverse_arity:i=1717:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:10_bd=off:sac=on:sas=z3:sos=on:i=967:si=on:rawr=on:rtra=on_0");
    // Improves by expected 241.99467069860924 probs costing 399965 Mi
    // Sub-schedule for 100000Mi strat cap / 800000Mi overall limit
    quick.push("lrs+1010_1:1_aac=none:bce=on:nicw=on:nm=0:plsq=on:plsql=on:sac=on:sos=on:sp=frequency:spb=units:to=lpo:i=523:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_atotf=0.1:bsr=unit_only:plsq=on:sd=1:sos=all:ss=included:i=3162:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_abs=on:amm=sco:anc=all_dependent:atotf=0.3:er=filter:fde=unused:fsd=on:fsdmm=1:newcnf=on:nwc=5.0:sac=on:sas=z3:slsq=on:slsqc=0:slsql=off:slsqr=34,509:ss=included:st=3.0:i=1639:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_drc=off:flr=on:nwc=2.0:sac=on:urr=ec_only:i=2320:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_ins=2:sd=1:ss=axioms:i=8270:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_ins=1:sd=1:sos=on:ss=axioms:to=lpo:i=6144:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_aac=none:bd=off:sac=on:sos=on:spb=units:i=17362:si=on:rawr=on:rtra=on_0");
    quick.push("ott+3_1:1_flr=on:gsp=on:lcm=predicate:plsq=on:plsqr=7,41:sac=on:sos=on:sp=frequency:spb=goal_then_units:urr=on:i=2360:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_5:1_br=off:fde=none:nwc=3.0:sd=1:sgt=10:sos=on:ss=axioms:urr=on:i=3493:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=4:sos=on:spb=goal:ss=axioms:st=3.7:to=lpo:urr=on:i=823:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=2:sos=on:ss=axioms:st=3.0:i=1720:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:28_av=off:bsr=on:cond=on:fde=none:fsd=on:gsp=on:irw=on:s2a=on:s2at=1.5:sims=off:slsq=on:slsqc=0:slsqr=5,3:i=3241:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_acc=on:anc=all_dependent:fde=none:ins=1:plsq=on:plsqr=9,4:slsq=on:slsqc=1:slsqr=5,4:i=2617:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:ep=RS:lcm=reverse:newcnf=on:s2a=on:s2at=3.0:i=2196:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1024_awrs=decay:awrsf=32:ep=RSTC:s2a=on:sd=1:skr=on:ss=axioms:st=2.0:i=3906:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:sos=on:ss=axioms:st=2.0:urr=on:i=3676:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+4_1:1_flr=on:s2a=on:s2at=3.0:s2pl=on:sd=1:sos=on:ss=included:i=721:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_amm=off:anc=all:avsq=on:br=off:bsr=unit_only:erd=off:flr=on:gsp=on:newcnf=on:nicw=on:nwc=10.0:rnwc=on:s2pl=no:skr=on:sp=reverse_frequency:spb=units:ss=axioms:st=1.74:updr=off:urr=on:i=3739:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bce=on:ep=RST:gsp=on:sd=1:sos=on:ss=axioms:urr=on:i=1704:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_ep=RS:newcnf=on:sac=on:urr=ec_only:i=3054:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_aac=none:avsq=on:avsqc=1:bd=off:newcnf=on:nm=4:nwc=5.0:s2a=on:sac=on:i=1679:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_10:13_abs=on:amm=off:anc=none:avsq=on:avsqc=1:avsqr=12,23:bsr=on:cond=on:drc=off:fd=preordered:fde=none:flr=on:fsr=off:gs=on:gsaa=full_model:gsem=off:ins=3:lcm=reverse:nwc=5.0:sas=z3:sims=off:skr=on:sos=on:sp=frequency:spb=units:to=lpo:updr=off:urr=on:i=544:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bce=on:dr=on:drc=off:fd=preordered:gs=on:newcnf=on:nm=2:sims=off:sp=frequency:to=lpo:i=8312:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_av=off:dr=on:ep=RS:mep=off:newcnf=on:nm=2:nwc=10.0:s2a=on:slsq=on:slsqc=0:slsqr=1,8:i=876:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:fd=off:fde=none:ins=3:sac=on:sos=on:spb=goal:to=lpo:i=921:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:gs=on:newcnf=on:nm=2:plsq=on:plsqr=32,1:sd=1:sos=all:ss=included:st=3.0:i=906:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_aac=none:add=off:alpa=false:amm=off:anc=all_dependent:bce=on:bs=on:cond=on:erd=off:fd=off:flr=on:fsr=off:irw=on:lwlo=on:newcnf=on:nm=0:nwc=6.0:rnwc=on:s2a=on:s2at=2.0:skr=on:spb=goal_then_units:urr=on:i=1305:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+0_1:1_br=off:drc=off:erd=off:urr=ec_only:i=946:si=on:rawr=on:rtra=on_0");
    quick.push("dis+3_1:16_av=off:lcm=reverse:nm=2:plsq=on:plsqr=319,32:s2a=on:s2at=2.0:sos=on:spb=goal:i=4450:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bsr=on:erd=off:nwc=5.0:plsq=on:plsqc=1:plsqr=107,4:s2a=on:s2at=1.5:sas=z3:sp=reverse_frequency:spb=units:updr=off:i=1114:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_8:1_av=off:bd=off:fd=off:sfv=off:sos=all:urr=ec_only:i=6278:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_45163:73544_aac=none:abs=on:add=large:afr=on:alpa=false:amm=off:anc=none:avsq=on:avsqr=57,253:bs=on:bsr=unit_only:cond=fast:ep=R:fde=unused:gsp=on:mep=off:nwc=4.0:skr=on:slsq=on:slsqc=2:slsql=off:slsqr=59173,778640:sp=occurrence:updr=off:i=7651:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=R:gsp=on:nm=0:sos=on:spb=units:ss=included:i=2058:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:1024_gsp=on:newcnf=on:nwc=2.0:s2a=on:s2at=3.0:sp=reverse_arity:spb=goal_then_units:updr=off:i=22061:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bs=unit_only:drc=off:fd=preordered:foolp=on:nwc=5.0:plsq=on:plsql=on:s2a=on:s2at=3.0:sp=frequency:to=lpo:uwa=interpreted_only:i=835:si=on:rawr=on:rtra=on_0");
    quick.push("dis+33_109:91_acc=model:aer=off:afr=on:alpa=false:bce=on:bs=on:cond=fast:drc=off:fde=none:foolp=on:gs=on:gsem=on:gsp=on:irw=on:nm=0:nwc=10.0:rnwc=on:s2a=on:s2at=2.0:slsq=on:slsqc=1:slsql=off:slsqr=1,4:spb=units:urr=ec_only:i=4532:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:4_drc=off:sos=on:to=lpo:i=801:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:ep=RSTC:sos=all:urr=on:i=996:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_fd=preordered:fsd=on:sos=on:thsq=on:thsqc=64:thsqd=32:uwa=ground:i=511:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:128_av=off:awrs=converge:awrsf=64:irw=on:lcm=reverse:nwc=10.0:sos=on:spb=units:thsq=on:thsqc=32:thsqr=1,2:i=1675:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_3:1_nm=0:s2a=on:s2at=2.0:spb=goal:to=lpo:urr=on:i=815:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_aac=none:bs=unit_only:ep=RS:gsp=on:nwc=5.0:rnwc=on:s2a=on:s2at=3.0:slsq=on:slsqc=2:slsqr=1,8:i=1235:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_fde=unused:nwc=10.0:s2a=on:s2at=3.0:sac=on:i=46327:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:6_aac=none:afr=on:bce=on:bsr=unit_only:canc=cautious:cond=fast:fde=unused:newcnf=on:nwc=3.0:s2a=on:s2agt=40:sas=z3:sfv=off:sp=weighted_frequency:spb=units:tha=off:to=lpo:i=9076:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_bd=preordered:drc=off:fd=preordered:fsr=off:plsq=on:i=1003:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1_1:1_abs=on:afq=1.0:atotf=0.1:avsq=on:drc=off:lcm=predicate:nwc=1.1:plsq=on:sp=unary_first:spb=units:i=2729:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:4_av=off:bd=off:drc=off:ins=1:nwc=2.0:spb=goal:tgt=full:to=lpo:i=911:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:14_awrs=converge:br=off:drc=off:ev=cautious:s2a=on:sfv=off:tgt=ground:tha=off:urr=on:i=14135:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_drc=off:fd=preordered:tgt=full:to=lpo:i=12718:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=18087:si=on:rawr=on:rtra=on_0");
    quick.push("ott+33_1873:56644_av=off:awrs=converge:cond=on:dr=on:er=known:fd=off:fsd=on:gsp=on:kws=inv_frequency:nm=15:nwc=2.0:plsq=on:plsqc=1:plsql=on:plsqr=7736796,616469:s2a=on:s2at=4.1:s2pl=on:sp=const_min:spb=goal:updr=off:uwa=all:i=7253:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_aac=none:er=known:nwc=3.0:i=331:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bd=off:canc=force:ev=cautious:nwc=5.0:i=1350:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=1676:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+3_1:1_atotf=0.2:fsr=off:kws=precedence:sp=weighted_frequency:spb=intro:tgt=ground:i=1849:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_aac=none:abs=on:er=known:fde=none:fsr=off:nwc=5.0:s2a=on:s2at=4.0:sp=const_frequency:to=lpo:urr=ec_only:i=24260:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_11:31_aac=none:add=off:afr=on:amm=sco:avsq=on:avsqc=1:avsql=on:avsqr=1,16:awrs=decay:awrsf=10:drc=off:er=filter:fde=none:foolp=on:kmz=on:kws=inv_arity_squared:nwc=3.0:slsq=on:slsqc=2:slsqr=1,4:spb=units:thsq=on:thsqc=32:thsqd=16:i=591:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:512_drc=off:fd=preordered:ins=2:kws=precedence:s2a=on:sp=unary_first:spb=intro:tgt=ground:i=5178:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1002_1:1_av=off:er=known:fde=unused:gve=cautious:irw=on:plsq=on:plsqc=1:plsqr=19,2:tgt=full:i=4531:si=on:rawr=on:rtra=on_0");
    quick.push("dis+22_1:28_av=off:bd=off:lcm=predicate:nm=4:nwc=2.0:plsq=on:plsqr=3,13:s2a=on:s2at=1.9:i=5995:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:nm=5:plsq=on:plsqc=1:plsqr=32,1:urr=on:i=9417:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_bsd=on:fde=none:fsd=on:s2a=on:s2agt=32:i=15889:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:64_bd=preordered:drc=off:s2a=on:spb=goal:tgt=ground:to=lpo:i=26550:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bsr=unit_only:cond=on:flr=on:newcnf=on:nwc=10.0:sas=z3:to=lpo:i=6132:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_anc=all:br=off:newcnf=on:s2a=on:s2at=2.0:sac=on:sd=1:ss=included:urr=on:i=7284:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1024_br=off:gsp=on:nm=4:sos=all:urr=on:i=4374:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_5:1_norm_ineq=on:sas=z3:sos=all:ss=axioms:tha=off:i=2150:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:1_aac=none:bsr=unit_only:ep=R:fde=none:nwc=10.0:sac=on:sas=z3:sos=all:i=4234:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_3:29_av=off:awrs=decay:awrsf=32:bce=on:drc=off:fde=unused:gsp=on:irw=on:nwc=2.0:spb=goal_then_units:updr=off:urr=ec_only:i=1649:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_39044:804583_anc=all:avsq=on:avsqr=302,909:awrs=decay:awrsf=20:bd=off:bsr=on:cond=on:gsp=on:nm=0:nwc=2.0:plsq=on:plsqr=9,13:s2a=on:s2agt=16:sac=on:thsq=on:thsqc=32:thsqd=32:thsql=off:to=lpo:updr=off:uwa=all:i=1174:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_br=off:fsr=off:gsp=on:slsq=on:slsqc=1:slsqr=1,2:urr=on:i=21641:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1_1:24_drc=off:fd=preordered:s2a=on:i=3807:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_s2a=on:sd=2:sos=on:ss=included:st=3.0:i=6831:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:128_abs=on:atotf=0.2:gsp=on:nwc=10.0:urr=on:i=10098:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_fmbas=predicate:i=2139:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_br=off:bsr=on:fsr=off:nwc=2.0:s2a=on:s2agt=12:s2at=5.0:urr=on:i=7859:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_fde=unused:fmbas=predicate:gsp=on:newcnf=on:nm=0:i=1947:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:5_bs=unit_only:drc=off:ins=1:nwc=2.16:rnwc=on:slsq=on:slsqr=13,149:sp=const_min:tgt=ground:to=lpo:uwa=interpreted_only:i=57692:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:sp=occurrence:i=15919:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1004_1:1_aac=none:fde=none:nwc=5.0:sd=1:ss=axioms:urr=ec_only:i=1848:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sos=all:ss=axioms:st=5.0:i=22148:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_sos=on:ss=axioms:i=3013:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_sd=3:sos=on:ss=axioms:i=2513:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_1:1_av=off:fde=unused:s2a=on:sos=on:ss=included:i=5726:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_ep=R:sd=2:sos=on:ss=axioms:i=5794:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_8:1_av=off:fde=unused:newcnf=on:nm=2:sd=2:sos=all:sp=const_max:ss=axioms:st=3.0:i=8538:si=on:rawr=on:rtra=on_0");
    quick.push("dis-10_1:1_ep=RS:fsr=off:gsp=on:sd=2:sos=on:ss=axioms:st=3.0:i=1713:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_3:1_av=off:bd=off:cond=fast:sd=2:sos=all:ss=axioms:i=2718:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_4:1_br=off:fde=none:s2a=on:sac=on:sd=3:ss=axioms:urr=on:i=7116:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1010_1:1_sd=2:sos=on:sp=occurrence:ss=axioms:urr=on:i=4771:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_nm=32:sas=z3:sd=1:sos=on:ss=axioms:i=996:si=on:rawr=on:rtra=on_0");
    quick.push("dis+2_1:1_av=off:lcm=predicate:nm=2:sd=2:sos=on:sp=const_min:ss=axioms:st=1.5:i=8264:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_4:1_cond=fast:fde=unused:lcm=predicate:nm=4:s2a=on:sd=3:sos=on:ss=axioms:st=2.0:i=15699:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=off:irw=on:lma=on:sd=2:sos=all:sp=const_min:ss=axioms:stl=40:i=60111:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_afq=1.1:anc=none:bd=off:sd=2:sos=on:ss=axioms:i=12185:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_afp=100000:afq=1.4:bd=preordered:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:sd=1:sos=all:sp=const_min:ss=axioms:i=8059:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_1:1_aac=none:add=large:anc=all_dependent:cond=fast:ep=RST:fsr=off:lma=on:nm=2:sos=on:sp=reverse_arity:stl=30:uhcvi=on:urr=on:i=1265:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1010_1:7_gsp=on:nwc=2.0:sd=2:sos=on:ss=axioms:st=1.5:i=3419:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_amm=off:cond=on:sd=3:sos=on:ss=axioms:st=1.5:i=1253:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_1:1_av=off:lcm=reverse:lma=on:sd=2:sos=all:ss=axioms:st=1.5:i=15194:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_anc=all:ep=RST:fde=unused:fsr=off:gsp=on:nm=16:sd=2:sos=on:ss=axioms:st=5.0:i=6215:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:5_acc=on:afp=1010:fsr=off:gsp=on:nm=10:sac=on:sos=on:sp=unary_first:urr=ec_only:i=57834:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:4_afp=10010:amm=off:anc=none:awrs=decay:awrsf=50:ep=RSTC:fde=unused:lma=on:nm=16:nwc=5.0:s2a=on:sp=frequency:urr=ec_only:i=1325:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:3_av=off:lcm=predicate:lma=on:sd=2:sos=all:sp=unary_first:ss=axioms:i=5958:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:nwc=2.0:sd=4:ss=axioms:st=3.0:i=1570:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_amm=off:br=off:nwc=5.0:rp=on:sfv=off:sos=all:ss=axioms:to=lpo:urr=ec_only:i=520:si=on:rawr=on:rtra=on_0");
    quick.push("dis+35_1:5_av=off:rp=on:s2a=on:slsq=on:slsqc=1:slsqr=1,4:sp=const_frequency:updr=off:i=1514:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_av=off:ep=RSTC:rp=on:sos=on:i=806:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_bd=off:sd=2:sos=on:ss=axioms:st=2.0:i=7766:si=on:rawr=on:rtra=on_0");
    quick.push("dis-10_3:2_amm=sco:ep=RS:fsr=off:nm=10:sd=2:sos=on:ss=axioms:st=3.0:i=2622:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:5_anc=all_dependent:bd=off:gsp=on:lma=on:newcnf=on:sac=on:sas=z3:sos=on:urr=ec_only:i=2700:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:5_cond=on:irw=on:nm=6:nwc=5.0:sas=z3:sd=10:ss=axioms:urr=on:i=3211:si=on:rawr=on:rtra=on_0");
    // Improves by expected 140.3280720782613 probs costing 799656 Mi
    // Sub-schedule for 150000Mi strat cap / 1200000Mi overall limit
    quick.push("dis+1010_1:1_abs=on:amm=sco:anc=all_dependent:atotf=0.3:er=filter:fde=unused:fsd=on:fsdmm=1:newcnf=on:nwc=5.0:sac=on:sas=z3:slsq=on:slsqc=0:slsql=off:slsqr=34,509:ss=included:st=3.0:i=1217:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_drc=off:flr=on:nwc=2.0:sac=on:urr=ec_only:i=2320:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:2_br=off:bs=unit_only:bsr=unit_only:nwc=5.0:s2a=on:s2agt=32:urr=on:i=15960:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:28_drc=off:fd=preordered:fsr=off:sp=frequency:to=lpo:i=1686:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_2:217_avsq=on:avsql=on:avsqr=5,12:awrs=decay:awrsf=3:bs=on:drc=off:nwc=3.0:ss=axioms:st=2.0:i=5300:si=on:rawr=on:rtra=on_0");
    quick.push("ott+3_1:1_flr=on:gsp=on:lcm=predicate:plsq=on:plsqr=7,41:sac=on:sos=on:sp=frequency:spb=goal_then_units:urr=on:i=2360:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_acc=on:anc=all_dependent:fde=none:ins=1:plsq=on:plsqr=9,4:slsq=on:slsqc=1:slsqr=5,4:i=2433:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1024_awrs=decay:awrsf=32:ep=RSTC:s2a=on:sd=1:skr=on:ss=axioms:st=2.0:i=3261:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_br=off:fd=off:fde=unused:s2a=on:sd=2:sos=all:ss=axioms:st=2.0:to=lpo:urr=on:i=6544:si=on:rawr=on:rtra=on_0");
    quick.push("dis+3_1:2_br=off:gs=on:nwc=5.0:s2a=on:s2at=2.5:urr=on:i=13411:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bce=on:ep=RST:gsp=on:sd=1:sos=on:ss=axioms:urr=on:i=1704:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_ep=RS:newcnf=on:sac=on:urr=ec_only:i=3054:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_aac=none:avsq=on:avsqc=1:bd=off:newcnf=on:nm=4:nwc=5.0:s2a=on:sac=on:i=1679:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sos=on:ss=included:st=1.2:urr=on:i=21564:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_3:1_abs=on:ep=RST:newcnf=on:nm=2:sas=z3:sd=1:sos=all:ss=included:to=lpo:i=149459:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:128_drc=off:sp=frequency:to=lpo:i=42301:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_av=off:dr=on:ep=RS:mep=off:newcnf=on:nm=2:nwc=10.0:s2a=on:slsq=on:slsqc=0:slsqr=1,8:i=1223:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:fd=off:fde=none:ins=3:sac=on:sos=on:spb=goal:to=lpo:i=921:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:2_abs=on:avsq=on:avsqc=2:bce=on:bsr=unit_only:cond=fast:ep=RS:erd=off:newcnf=on:s2a=on:urr=ec_only:i=2613:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:gs=on:newcnf=on:nm=2:plsq=on:plsqr=32,1:sd=1:sos=all:ss=included:st=3.0:i=906:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:3_br=off:gsp=on:lwlo=on:nwc=5.0:plsq=on:plsql=on:plsqr=3423,254:s2a=on:slsq=on:slsqc=2:slsql=off:slsqr=1,4:urr=on:i=29510:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_45163:73544_aac=none:abs=on:add=large:afr=on:alpa=false:amm=off:anc=none:avsq=on:avsqr=57,253:bs=on:bsr=unit_only:cond=fast:ep=R:fde=unused:gsp=on:mep=off:nwc=4.0:skr=on:slsq=on:slsqc=2:slsql=off:slsqr=59173,778640:sp=occurrence:updr=off:i=7652:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=R:gsp=on:nm=0:sos=on:spb=units:ss=included:i=2058:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_1:1024_av=off:dr=on:gsp=on:s2a=on:s2at=2.7:s2pl=no:skr=on:slsq=on:slsqc=0:slsqr=1,1:i=11180:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1004_1:1024_av=off:gsp=on:newcnf=on:sos=all:i=9351:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_flr=on:ss=included:st=1.4:i=26716:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bs=unit_only:drc=off:fd=preordered:foolp=on:nwc=5.0:plsq=on:plsql=on:s2a=on:s2at=3.0:sp=frequency:to=lpo:uwa=interpreted_only:i=835:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=9658:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_atotf=0.1:avsq=on:avsqc=2:avsqr=1,16:br=off:cond=fast:lwlo=on:nicw=on:nwc=3.0:sac=on:sas=z3:urr=on:i=12311:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:28_bsr=unit_only:flr=on:sos=on:i=5892:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:128_av=off:awrs=converge:awrsf=64:irw=on:lcm=reverse:nwc=10.0:sos=on:spb=units:thsq=on:thsqc=32:thsqr=1,2:i=1675:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_aac=none:bs=unit_only:ep=RS:gsp=on:nwc=5.0:rnwc=on:s2a=on:s2at=3.0:slsq=on:slsqc=2:slsqr=1,8:i=9215:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_fde=unused:nwc=10.0:s2a=on:s2at=3.0:sac=on:i=86090:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_26459:191296_av=off:awrs=converge:awrsf=30:bd=preordered:bs=unit_only:drc=off:etr=on:flr=on:lwlo=on:nwc=5.0:plsq=on:plsqc=1:plsql=on:plsqr=1,32:skr=on:slsq=on:slsqr=18,107:sp=const_min:tgt=ground:to=lpo:urr=ec_only:i=9411:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_3:1_av=off:br=off:bsd=on:bsr=on:etr=on:fsd=on:gsp=on:kws=precedence:nwc=10.0:plsq=on:plsqr=2,61:s2at=3.0:slsq=on:slsqc=2:slsqr=1,2:spb=units:tgt=ground:thsq=on:thsqc=16:thsqd=1:updr=off:urr=on:i=1437:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:4_av=off:bd=off:drc=off:ins=1:nwc=2.0:spb=goal:tgt=full:to=lpo:i=12116:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:28_afr=on:anc=all_dependent:bs=on:bsr=unit_only:nicw=on:sp=const_frequency:uhcvi=on:i=38057:si=on:rawr=on:rtra=on_0");
    quick.push("dis+22_3:1_fde=none:nm=16:nwc=10.0:s2a=on:s2at=2.0:urr=ec_only:i=19028:si=on:rawr=on:rtra=on_0");
    quick.push("ott+33_1873:56644_av=off:awrs=converge:cond=on:dr=on:er=known:fd=off:fsd=on:gsp=on:kws=inv_frequency:nm=15:nwc=2.0:plsq=on:plsqc=1:plsql=on:plsqr=7736796,616469:s2a=on:s2at=4.1:s2pl=on:sp=const_min:spb=goal:updr=off:uwa=all:i=5587:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_4:1_abs=on:afp=20:amm=off:anc=all:bd=off:br=off:canc=force:s2a=on:sas=z3:slsq=on:urr=on:i=9875:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:12_drc=off:fd=preordered:tgt=full:i=59873:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=1676:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1024_av=off:erd=off:fde=none:s2agt=32:slsq=on:slsqc=1:i=2082:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_fde=unused:fs=off:fsr=off:ins=1:nwc=5.0:s2agt=64:slsq=on:slsqc=1:tgt=full:urr=on:i=37418:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:nm=5:plsq=on:plsqc=1:plsqr=32,1:urr=on:i=3356:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bsr=unit_only:cond=on:flr=on:newcnf=on:nwc=10.0:sas=z3:to=lpo:i=6132:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:4_av=off:bd=off:br=off:fsr=off:plsq=on:plsqr=20,11:s2a=on:urr=ec_only:i=7141:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_2:1_av=off:fsr=off:lcm=predicate:nm=2:nwc=3.0:plsq=on:s2a=on:s2agt=47:slsq=on:slsqc=1:slsqr=1,4:sp=reverse_arity:spb=goal_then_units:i=4289:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+0_1:1_av=off:bs=on:bsr=on:cond=fast:foolp=on:gsp=on:lwlo=on:nm=2:thsq=on:thsqc=64:uwa=one_side_interpreted:i=13011:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_fmbas=predicate:i=2025:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_drc=off:sos=all:sp=unary_first:tgt=full:urr=ec_only:i=41475:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:128_aac=none:acc=on:amm=off:atotf=0.1:bd=preordered:drc=off:fd=preordered:fde=none:gs=on:nicw=on:s2a=on:s2at=5.0:slsq=on:sp=const_max:spb=non_intro:tgt=ground:to=lpo:i=96858:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_fde=unused:fmbas=predicate:gsp=on:newcnf=on:nm=0:i=1868:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_5:1_acc=model:br=off:nicw=on:s2a=on:ss=axioms:urr=on:i=3105:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_sos=on:ss=axioms:i=3013:si=on:rawr=on:rtra=on_0");
    quick.push("ott+4_1:40_av=off:nm=0:sos=all:i=57197:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_1:1_av=off:fde=unused:s2a=on:sos=on:ss=included:i=14431:si=on:rawr=on:rtra=on_0");
    quick.push("lrs-11_1:1_gsp=on:lma=on:nm=6:sd=3:sos=all:sp=reverse_arity:ss=axioms:st=1.2:stl=30:urr=on:i=8725:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_2:1_av=off:lwlo=on:newcnf=on:nm=16:nwc=2.0:sd=4:sp=frequency:ss=axioms:i=13187:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_ep=R:sd=2:sos=on:ss=axioms:i=7667:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=1:ss=axioms:st=5.0:urr=on:i=5101:si=on:rawr=on:rtra=on_0");
    quick.push("dis-10_1:1_ep=RS:fsr=off:gsp=on:sd=2:sos=on:ss=axioms:st=3.0:i=1713:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:6_acc=model:fsr=off:nwc=1.1:sac=on:sos=on:urr=ec_only:i=47125:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:16_add=large:anc=none:bce=on:bs=on:gs=on:nwc=6.0:sp=occurrence:updr=off:i=4366:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_add=large:afp=100000:afq=2.0:amm=off:anc=none:cond=fast:fde=none:gs=on:gsem=off:lma=on:newcnf=on:nm=64:sos=on:sp=reverse_arity:ss=axioms:i=1550:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_4:1_br=off:gsp=on:nwc=2.0:s2a=on:sac=on:ss=axioms:urr=on:i=16871:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:1_lwlo=on:nwc=10.0:i=14688:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_add=large:afq=1.4:bd=off:newcnf=on:nm=32:sos=all:ss=included:urr=on:i=4765:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_anc=all:ep=RST:fde=unused:fsr=off:gsp=on:nm=16:sd=2:sos=on:ss=axioms:st=5.0:i=6215:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:1_nwc=3.0:sos=on:ss=axioms:i=3102:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bd=off:fd=preordered:fde=unused:rp=on:sfv=off:sos=on:sp=reverse_frequency:spb=goal:to=lpo:i=1709:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:5_av=off:flr=on:fsr=off:rp=on:sp=occurrence:ss=axioms:i=6031:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:rp=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=52867:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:1_av=off:nwc=2.0:sos=theory:sp=const_frequency:updr=off:urr=ec_only:i=10842:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_bd=off:sd=2:sos=on:ss=axioms:st=2.0:i=7766:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_bd=off:sd=2:sos=on:ss=axioms:st=2.0:i=14378:si=on:rawr=on:rtra=on_0");
    quick.push("dis-10_3:2_amm=sco:ep=RS:fsr=off:nm=10:sd=2:sos=on:ss=axioms:st=3.0:i=2622:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:5_anc=all_dependent:bd=off:gsp=on:lma=on:newcnf=on:sac=on:sas=z3:sos=on:urr=ec_only:i=2700:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:10_bd=off:sac=on:sas=z3:sos=on:i=21500:si=on:rawr=on:rtra=on_0");
    // Improves by expected 94.28030220941935 probs costing 1197931 Mi
    // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
    quick.push("lrs+1011_1:5_av=off:awrs=decay:awrsf=97:bce=on:bsr=on:drc=off:flr=on:gs=on:ins=3:lwlo=on:newcnf=on:nm=0:plsq=on:plsqr=4437,256:s2a=on:s2at=4.0:s2pl=no:sims=off:skr=on:slsq=on:slsqc=0:slsqr=31,16:sos=all:sp=frequency:updr=off:i=24409:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_abs=on:amm=sco:anc=all_dependent:atotf=0.3:er=filter:fde=unused:fsd=on:fsdmm=1:newcnf=on:nwc=5.0:sac=on:sas=z3:slsq=on:slsqc=0:slsql=off:slsqr=34,509:ss=included:st=3.0:i=1217:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_drc=off:flr=on:nwc=2.0:sac=on:urr=ec_only:i=2320:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_ins=2:sd=1:ss=axioms:i=4177:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ep=R:newcnf=on:sd=2:ss=axioms:i=16584:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_ins=1:sd=1:sos=on:ss=axioms:to=lpo:i=6144:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_av=off:bce=on:bd=off:bsr=on:flr=on:to=lpo:i=12243:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_acc=on:anc=all_dependent:fde=none:ins=1:plsq=on:plsqr=9,4:slsq=on:slsqc=1:slsqr=5,4:i=2433:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:128_av=off:bd=off:bsr=unit_only:fd=preordered:to=lpo:updr=off:i=173132:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1024_awrs=decay:awrsf=32:ep=RSTC:s2a=on:sd=1:skr=on:ss=axioms:st=2.0:i=3261:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_br=off:fd=off:fde=unused:s2a=on:sd=2:sos=all:ss=axioms:st=2.0:to=lpo:urr=on:i=6544:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_cond=fast:newcnf=on:plsq=on:sos=all:spb=goal:to=lpo:urr=on:i=4893:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_nwc=3.0:sd=1:spb=goal_then_units:ss=included:to=lpo:i=3486:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_nwc=2.0:ss=axioms:st=1.3:urr=on:i=41492:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_nwc=5.0:sd=4:sp=occurrence:ss=included:to=lpo:i=146178:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=1:sos=on:ss=included:i=4074:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_erd=off:s2a=on:s2at=2.0:sac=on:i=25162:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bce=on:ep=RST:gsp=on:sd=1:sos=on:ss=axioms:urr=on:i=17628:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sos=on:ss=included:st=1.2:urr=on:i=225823:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_3:1_abs=on:ep=RST:newcnf=on:nm=2:sas=z3:sd=1:sos=all:ss=included:to=lpo:i=280789:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_av=off:newcnf=on:i=30371:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:fd=off:fde=none:ins=3:sac=on:sos=on:spb=goal:to=lpo:i=921:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_ss=included:st=1.5:i=29566:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:ep=RSTC:plsq=on:plsqc=1:plsqr=32,1:urr=on:i=52461:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_45163:73544_aac=none:abs=on:add=large:afr=on:alpa=false:amm=off:anc=none:avsq=on:avsqr=57,253:bs=on:bsr=unit_only:cond=fast:ep=R:fde=unused:gsp=on:mep=off:nwc=4.0:skr=on:slsq=on:slsqc=2:slsql=off:slsqr=59173,778640:sp=occurrence:updr=off:i=17746:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=R:gsp=on:nm=0:sos=on:spb=units:ss=included:i=2058:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1004_1:1024_av=off:gsp=on:newcnf=on:sos=all:i=9351:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:1024_gsp=on:newcnf=on:nwc=2.0:s2a=on:s2at=3.0:sp=reverse_arity:spb=goal_then_units:updr=off:i=36962:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1024_afp=20:afq=2.0:anc=all:bd=preordered:bs=unit_only:drc=off:sac=on:sos=on:to=lpo:i=62595:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bs=unit_only:drc=off:fd=preordered:foolp=on:nwc=5.0:plsq=on:plsql=on:s2a=on:s2at=3.0:sp=frequency:to=lpo:uwa=interpreted_only:i=835:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_397:95149_awrs=decay:awrsf=30:s2a=on:urr=on:i=34407:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=5736:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_av=off:fsr=off:nm=6:plsq=on:s2a=on:s2at=3.0:slsq=on:slsqc=0:slsqr=1,8:sp=frequency:to=lpo:i=11744:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1_27:428_av=off:awrs=converge:awrsf=8:bsr=unit_only:drc=off:fd=preordered:newcnf=on:nwc=1.5:skr=on:slsq=on:slsqc=2:slsql=off:slsqr=1,4:sp=reverse_frequency:uwa=one_side_constant:i=24319:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_atotf=0.1:erd=off:fde=none:gsp=on:urr=on:i=2662:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_aac=none:bs=unit_only:ep=RS:gsp=on:nwc=5.0:rnwc=on:s2a=on:s2at=3.0:slsq=on:slsqc=2:slsqr=1,8:i=9215:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_aac=none:bsr=on:ep=R:fsr=off:lma=on:sos=all:i=13001:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_fde=unused:nwc=10.0:s2a=on:s2at=3.0:sac=on:i=108631:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:3_br=off:nwc=2.0:s2a=on:s2agt=64:slsq=on:slsqc=1:slsqr=1,2:urr=on:i=11425:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:64_bd=preordered:nwc=5.0:to=lpo:uwa=one_side_interpreted:i=32754:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1_1:1_abs=on:afq=1.0:atotf=0.1:avsq=on:drc=off:lcm=predicate:nwc=1.1:plsq=on:sp=unary_first:spb=units:i=2729:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_awrs=converge:drc=off:kws=inv_frequency:tgt=full:i=46774:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_26459:191296_av=off:awrs=converge:awrsf=30:bd=preordered:bs=unit_only:drc=off:etr=on:flr=on:lwlo=on:nwc=5.0:plsq=on:plsqc=1:plsql=on:plsqr=1,32:skr=on:slsq=on:slsqr=18,107:sp=const_min:tgt=ground:to=lpo:urr=ec_only:i=8899:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:4_av=off:bd=off:drc=off:ins=1:nwc=2.0:spb=goal:tgt=full:to=lpo:i=37361:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_drc=off:fd=preordered:tgt=full:to=lpo:i=62176:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=13358:si=on:rawr=on:rtra=on_0");
    quick.push("dis+22_3:1_fde=none:nm=16:nwc=10.0:s2a=on:s2at=2.0:urr=ec_only:i=40798:si=on:rawr=on:rtra=on_0");
    quick.push("dis+20_1:12_aac=none:acc=model:awrs=converge:fd=preordered:fsr=off:nicw=on:nwc=3.0:s2a=on:s2agt=16:spb=goal:to=lpo:i=83118:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=42006:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_av=off:tgt=ground:i=5977:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_av=off:er=known:fd=preordered:foolp=on:gs=on:nwc=5.0:s2at=4.2:slsq=on:slsqc=1:slsqr=1,8:tgt=full:urr=ec_only:uwa=all:i=23447:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:nm=5:plsq=on:plsqc=1:plsqr=32,1:urr=on:i=9417:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:128_drc=off:ins=1:sp=const_frequency:tgt=ground:i=10938:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:br=off:sas=z3:spb=goal:tgt=full:tha=some:to=lpo:uwa=all:i=110001:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_bsd=on:fde=none:fsd=on:s2a=on:s2agt=32:i=15889:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bsr=unit_only:cond=on:flr=on:newcnf=on:nwc=10.0:sas=z3:to=lpo:i=6132:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_anc=all:br=off:newcnf=on:s2a=on:s2at=2.0:sac=on:sd=1:ss=included:urr=on:i=12824:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_2:1_av=off:fsr=off:lcm=predicate:nm=2:nwc=3.0:plsq=on:s2a=on:s2agt=47:slsq=on:slsqc=1:slsqr=1,4:sp=reverse_arity:spb=goal_then_units:i=4289:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_atotf=0.2:drc=off:erd=off:fde=none:gsp=on:urr=on:i=3384:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_8:1_alpa=true:amm=off:bce=on:br=off:bs=on:bsr=unit_only:ep=R:flr=on:fsr=off:gsp=on:ins=1:nwc=3.0:sos=all:urr=on:i=2701:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+0_1:1_av=off:bs=on:bsr=on:cond=fast:foolp=on:gsp=on:lwlo=on:nm=2:thsq=on:thsqc=64:uwa=one_side_interpreted:i=40007:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_s2a=on:sd=2:sos=on:ss=included:st=3.0:i=6831:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:10_bs=on:drc=off:fd=preordered:fde=unused:foolp=on:nwc=3.0:spb=units:to=lpo:urr=ec_only:i=47611:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_3:1_av=off:awrs=decay:awrsf=8:bd=off:br=off:fd=preordered:ins=1:lma=on:nwc=3.0:plsq=on:plsqc=1:plsqr=1,32:s2a=on:s2agt=8:sp=unary_first:tgt=full:urr=on:uwa=interpreted_only:i=28797:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_drc=off:sos=all:sp=unary_first:tgt=full:urr=ec_only:i=47137:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_br=off:bsr=on:fsr=off:nwc=2.0:s2a=on:s2agt=12:s2at=5.0:urr=on:i=7859:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:128_aac=none:acc=on:amm=off:atotf=0.1:bd=preordered:drc=off:fd=preordered:fde=none:gs=on:nicw=on:s2a=on:s2at=5.0:slsq=on:sp=const_max:spb=non_intro:tgt=ground:to=lpo:i=95833:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_fde=unused:fmbas=predicate:gsp=on:newcnf=on:nm=0:i=6588:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:5_bs=unit_only:drc=off:ins=1:nwc=2.16:rnwc=on:slsq=on:slsqr=13,149:sp=const_min:tgt=ground:to=lpo:uwa=interpreted_only:i=69078:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sos=all:ss=axioms:st=5.0:i=22148:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_sos=on:ss=axioms:i=3013:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_2:3_av=off:cond=on:lwlo=on:nwc=2.0:i=329612:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_av=off:sp=frequency:updr=off:urr=ec_only:i=6982:si=on:rawr=on:rtra=on_0");
    quick.push("lrs-11_1:1_gsp=on:lma=on:nm=6:sd=3:sos=all:sp=reverse_arity:ss=axioms:st=1.2:stl=30:urr=on:i=7068:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_ep=R:sd=2:sos=on:ss=axioms:i=5794:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_8:1_av=off:fde=unused:newcnf=on:nm=2:sd=2:sos=all:sp=const_max:ss=axioms:st=3.0:i=7713:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=1:ss=axioms:st=5.0:urr=on:i=5101:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_av=off:nm=2:sd=3:sos=on:ss=axioms:st=1.2:i=4101:si=on:rawr=on:rtra=on_0");
    quick.push("dis-10_1:1_ep=RS:fsr=off:gsp=on:sd=2:sos=on:ss=axioms:st=3.0:i=1713:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:16_add=large:anc=none:bce=on:bs=on:gs=on:nwc=6.0:sp=occurrence:updr=off:i=14229:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:16_awrs=decay:awrsf=260:bsr=on:er=known:gsp=on:newcnf=on:nwc=3.0:s2a=on:sas=z3:sd=4:ss=axioms:i=2829:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1010_1:1_sd=2:sos=on:sp=occurrence:ss=axioms:urr=on:i=20142:si=on:rawr=on:rtra=on_0");
    quick.push("dis+2_1:1_av=off:lcm=predicate:nm=2:sd=2:sos=on:sp=const_min:ss=axioms:st=1.5:i=68603:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_4:1_cond=fast:fde=unused:lcm=predicate:nm=4:s2a=on:sd=3:sos=on:ss=axioms:st=2.0:i=15699:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_4:1_br=off:fde=unused:nm=16:s2a=on:sd=3:sp=frequency:ss=axioms:urr=on:i=12633:si=on:rawr=on:rtra=on_0");
    quick.push("ott-3_2:1_acc=on:add=large:anc=none:fde=none:gsp=on:irw=on:nm=0:s2a=on:sd=4:sos=on:ss=axioms:st=1.2:urr=on:i=59001:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_acc=on:urr=ec_only:i=33643:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_2:3_av=off:lcm=predicate:lma=on:sd=2:sos=all:ss=axioms:i=5917:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_av=off:gsp=on:lcm=predicate:newcnf=on:nm=2:sd=3:sos=on:ss=axioms:i=6651:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_nwc=5.0:sd=4:ss=included:st=5.0:i=15291:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_afq=1.1:anc=none:bd=off:sd=2:sos=on:ss=axioms:i=22625:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_add=large:afq=1.4:bd=off:newcnf=on:nm=32:sos=all:ss=included:urr=on:i=4765:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1010_1:7_gsp=on:nwc=2.0:sd=2:sos=on:ss=axioms:st=1.5:i=8460:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_bd=off:sd=2:sos=all:sp=unary_frequency:ss=axioms:i=123112:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_3:2_br=off:sas=z3:sd=3:sos=all:ss=axioms:st=3.0:urr=on:i=6812:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_av=off:gs=on:gsp=on:irw=on:nwc=2.0:sd=2:sos=on:ss=axioms:stl=30:urr=on:i=28205:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:5_er=filter:nwc=6.0:sd=2:sos=on:ss=axioms:st=1.5:i=10509:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_ep=R:sd=1:sos=all:ss=axioms:i=7726:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_anc=all:ep=RST:fde=unused:fsr=off:gsp=on:nm=16:sd=2:sos=on:ss=axioms:st=5.0:i=6215:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:5_acc=on:afp=1010:fsr=off:gsp=on:nm=10:sac=on:sos=on:sp=unary_first:urr=ec_only:i=69678:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:1_nwc=3.0:sos=on:ss=axioms:i=3102:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bd=off:fd=preordered:fde=unused:rp=on:sfv=off:sos=on:sp=reverse_frequency:spb=goal:to=lpo:i=1709:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:5_av=off:flr=on:fsr=off:rp=on:sp=occurrence:ss=axioms:i=5134:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:rp=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=283298:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:rp=on:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=315990:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=5:sp=occurrence:ss=axioms:st=3.0:i=3941:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:1_av=off:nwc=2.0:sos=theory:sp=const_frequency:updr=off:urr=ec_only:i=10826:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_bd=off:sd=2:sos=on:ss=axioms:st=2.0:i=7766:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_bd=off:sd=2:sos=on:ss=axioms:st=2.0:i=12190:si=on:rawr=on:rtra=on_0");
    quick.push("dis-10_3:2_amm=sco:ep=RS:fsr=off:nm=10:sd=2:sos=on:ss=axioms:st=3.0:i=1792:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:5_anc=all_dependent:bd=off:gsp=on:lma=on:newcnf=on:sac=on:sas=z3:sos=on:urr=ec_only:i=2700:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:5_cond=on:irw=on:nm=6:nwc=5.0:sas=z3:sd=10:ss=axioms:urr=on:i=3211:si=on:rawr=on:rtra=on_0");
    // Improves by expected 118.59731584823687 probs costing 3993203 Mi
    // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
    quick.push("lrs+1011_1:5_av=off:awrs=decay:awrsf=97:bce=on:bsr=on:drc=off:flr=on:gs=on:ins=3:lwlo=on:newcnf=on:nm=0:plsq=on:plsqr=4437,256:s2a=on:s2at=4.0:s2pl=no:sims=off:skr=on:slsq=on:slsqc=0:slsqr=31,16:sos=all:sp=frequency:updr=off:i=15218:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_abs=on:amm=sco:anc=all_dependent:atotf=0.3:er=filter:fde=unused:fsd=on:fsdmm=1:newcnf=on:nwc=5.0:sac=on:sas=z3:slsq=on:slsqc=0:slsql=off:slsqr=34,509:ss=included:st=3.0:i=1639:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ep=R:newcnf=on:sd=2:ss=axioms:i=16584:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1004_4:1_bd=off:sd=1:sims=off:skr=on:sos=all:ss=axioms:st=2.0:i=22600:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1024_awrs=decay:awrsf=32:ep=RSTC:s2a=on:sd=1:skr=on:ss=axioms:st=2.0:i=2223:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sgt=8:ss=axioms:i=15253:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_erd=off:s2a=on:s2at=2.0:sac=on:i=25162:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bce=on:ep=RST:gsp=on:sd=1:sos=on:ss=axioms:urr=on:i=17628:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sos=on:ss=included:st=1.2:urr=on:i=207899:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:8_av=off:bce=on:bs=unit_only:cond=on:dr=on:ep=RST:gs=on:gsp=on:mep=off:nm=10:nwc=2.0:plsq=on:plsqc=1:plsqr=2133,101:skr=on:sp=reverse_frequency:spb=units:updr=off:urr=ec_only:i=50027:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_45163:73544_aac=none:abs=on:add=large:afr=on:alpa=false:amm=off:anc=none:avsq=on:avsqr=57,253:bs=on:bsr=unit_only:cond=fast:ep=R:fde=unused:gsp=on:mep=off:nwc=4.0:skr=on:slsq=on:slsqc=2:slsql=off:slsqr=59173,778640:sp=occurrence:updr=off:i=13167:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=R:gsp=on:nm=0:sos=on:spb=units:ss=included:i=148943:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_br=off:gsp=on:nm=4:skr=on:urr=on:i=163792:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_flr=on:ss=included:st=1.4:i=26716:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_397:95149_awrs=decay:awrsf=30:s2a=on:urr=on:i=34407:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_av=off:fsr=off:nm=6:plsq=on:s2a=on:s2at=3.0:slsq=on:slsqc=0:slsqr=1,8:sp=frequency:to=lpo:i=12500:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1024_afp=1000:avsq=on:awrs=converge:bd=preordered:drc=off:ins=1:ss=axioms:st=5.0:to=lpo:uwa=interpreted_only:i=144525:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:50_awrs=converge:awrsf=60:drc=off:plsq=on:plsqr=1,32:spb=goal:i=48460:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ep=RS:fsr=off:sos=all:i=11579:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_aac=none:bs=unit_only:ep=RS:gsp=on:nwc=5.0:rnwc=on:s2a=on:s2at=3.0:slsq=on:slsqc=2:slsqr=1,8:i=5629:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_aac=none:bsr=on:ep=R:fsr=off:lma=on:sos=all:i=13001:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_fde=unused:nwc=10.0:s2a=on:s2at=3.0:sac=on:i=395635:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_av=off:bsr=on:nwc=3.0:urr=on:i=70330:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:4_av=off:bd=off:drc=off:ins=1:nwc=2.0:spb=goal:tgt=full:to=lpo:i=37361:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:12_drc=off:fd=preordered:tgt=full:i=266597:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=27990:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_34:25_av=off:awrs=decay:awrsf=23:bce=on:cond=on:flr=on:irw=on:kws=precedence:s2a=on:s2agt=30:s2at=3.2:slsq=on:slsqr=1,4:sp=const_min:spb=intro:updr=off:urr=ec_only:i=19276:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:32_abs=on:awrs=decay:awrsf=256:canc=force:sac=on:sas=z3:tgt=ground:tha=off:to=lpo:i=116329:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_av=off:tgt=ground:i=5977:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_av=off:er=known:fd=preordered:foolp=on:gs=on:nwc=5.0:s2at=4.2:slsq=on:slsqc=1:slsqr=1,8:tgt=full:urr=ec_only:uwa=all:i=14853:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_aac=none:abs=on:er=known:fde=none:fsr=off:nwc=5.0:s2a=on:s2at=4.0:sp=const_frequency:to=lpo:urr=ec_only:i=17516:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:nm=5:plsq=on:plsqc=1:plsqr=32,1:urr=on:i=9417:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:128_drc=off:ins=1:sp=const_frequency:tgt=ground:i=10938:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_2:3_av=off:fde=unused:nwc=5.0:tgt=ground:i=59537:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_bsd=on:fde=none:fsd=on:s2a=on:s2agt=32:i=15889:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:64_bd=preordered:drc=off:s2a=on:spb=goal:tgt=ground:to=lpo:i=25118:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+31_1:1_fs=off:fsr=off:kws=precedence:i=130001:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bsr=unit_only:cond=on:flr=on:newcnf=on:nwc=10.0:sas=z3:to=lpo:i=6132:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_atotf=0.2:drc=off:erd=off:fde=none:gsp=on:urr=on:i=3384:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:128_aac=none:acc=on:amm=off:atotf=0.1:bd=preordered:drc=off:fd=preordered:fde=none:gs=on:nicw=on:s2a=on:s2at=5.0:slsq=on:sp=const_max:spb=non_intro:tgt=ground:to=lpo:i=108833:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:sp=occurrence:i=15871:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_4_afp=100000:afq=1.2:anc=none:bd=off:cond=on:gs=on:gsem=off:nm=64:nwc=1:sd=2:sos=all:ss=axioms:st=2.0:updr=off:i=23881:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sos=all:ss=axioms:st=5.0:i=21624:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_av=off:sp=frequency:updr=off:urr=ec_only:i=6982:si=on:rawr=on:rtra=on_0");
    quick.push("lrs-11_1:1_gsp=on:lma=on:nm=6:sd=3:sos=all:sp=reverse_arity:ss=axioms:st=1.2:stl=30:urr=on:i=7068:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_ep=R:sd=2:sos=on:ss=axioms:i=5794:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=1:ss=axioms:st=5.0:urr=on:i=5101:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_4:1_br=off:fde=none:s2a=on:sac=on:sd=3:ss=axioms:urr=on:i=14829:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:6_acc=model:fsr=off:nwc=1.1:sac=on:sos=on:urr=ec_only:i=34391:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:16_add=large:anc=none:bce=on:bs=on:gs=on:nwc=6.0:sp=occurrence:updr=off:i=7197:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:16_awrs=decay:awrsf=260:bsr=on:er=known:gsp=on:newcnf=on:nwc=3.0:s2a=on:sas=z3:sd=4:ss=axioms:i=18702:si=on:rawr=on:rtra=on_0");
    quick.push("dis+2_1:1_av=off:lcm=predicate:nm=2:sd=2:sos=on:sp=const_min:ss=axioms:st=1.5:i=68603:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_4:1_br=off:gsp=on:nwc=2.0:s2a=on:sac=on:ss=axioms:urr=on:i=20075:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_4:1_br=off:fde=unused:nm=16:s2a=on:sd=3:sp=frequency:ss=axioms:urr=on:i=12633:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:1_lwlo=on:nwc=10.0:i=13206:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=off:irw=on:lma=on:sd=2:sos=all:sp=const_min:ss=axioms:stl=40:i=13499:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_av=off:gsp=on:lcm=predicate:newcnf=on:nm=2:sd=3:sos=on:ss=axioms:i=5569:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_nwc=5.0:sd=4:ss=included:st=5.0:i=15249:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_afq=1.1:anc=none:bd=off:sd=2:sos=on:ss=axioms:i=22625:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_afp=100000:afq=1.4:bd=preordered:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:sd=1:sos=all:sp=const_min:ss=axioms:i=188205:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_bd=off:sd=2:sos=all:sp=unary_frequency:ss=axioms:i=29131:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_av=off:gs=on:gsp=on:irw=on:nwc=2.0:sd=2:sos=on:ss=axioms:stl=30:urr=on:i=28205:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_1:1_aac=none:acc=on:add=large:bd=off:bs=unit_only:bsr=on:cond=on:nm=0:sac=on:sd=3:sos=on:ss=axioms:st=2.0:i=77426:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:5_er=filter:nwc=6.0:sd=2:sos=on:ss=axioms:st=1.5:i=13448:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_anc=all:ep=RST:fde=unused:fsr=off:gsp=on:nm=16:sd=2:sos=on:ss=axioms:st=5.0:i=6215:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:5_acc=on:afp=1010:fsr=off:gsp=on:nm=10:sac=on:sos=on:sp=unary_first:urr=ec_only:i=69362:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bd=off:fd=preordered:fde=unused:rp=on:sfv=off:sos=on:sp=reverse_frequency:spb=goal:to=lpo:i=2412:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:5_av=off:flr=on:fsr=off:rp=on:sp=occurrence:ss=axioms:i=6031:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:rp=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=283298:si=on:rawr=on:rtra=on_0");
    quick.push("dis+3_1:64_av=off:cond=on:lcm=reverse:nwc=3.0:sos=on:updr=off:i=92402:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_afp=100000:gsp=on:lwlo=on:nwc=3.0:sac=on:i=306399:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:10_bd=off:sac=on:sas=z3:sos=on:i=225114:si=on:rawr=on:rtra=on_0");
    // Improves by expected 41.96037081342004 probs costing 3998540 Mi
    // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
    quick.push("lrs+10_1:1_ep=R:newcnf=on:sd=2:ss=axioms:i=16584:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1004_4:1_bd=off:sd=1:sims=off:skr=on:sos=all:ss=axioms:st=2.0:i=22600:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1024_awrs=decay:awrsf=32:ep=RSTC:s2a=on:sd=1:skr=on:ss=axioms:st=2.0:i=3261:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_nwc=2.0:ss=axioms:st=1.3:urr=on:i=41492:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_erd=off:s2a=on:s2at=2.0:sac=on:i=25162:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bce=on:ep=RST:gsp=on:sd=1:sos=on:ss=axioms:urr=on:i=19579:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_3:1_abs=on:ep=RST:newcnf=on:nm=2:sas=z3:sd=1:sos=all:ss=included:to=lpo:i=406982:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:128_drc=off:sp=frequency:to=lpo:i=35338:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_ss=included:st=1.5:i=33482:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_45163:73544_aac=none:abs=on:add=large:afr=on:alpa=false:amm=off:anc=none:avsq=on:avsqr=57,253:bs=on:bsr=unit_only:cond=fast:ep=R:fde=unused:gsp=on:mep=off:nwc=4.0:skr=on:slsq=on:slsqc=2:slsql=off:slsqr=59173,778640:sp=occurrence:updr=off:i=17746:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=R:gsp=on:nm=0:sos=on:spb=units:ss=included:i=148943:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1024_afp=20:afq=2.0:anc=all:bd=preordered:bs=unit_only:drc=off:sac=on:sos=on:to=lpo:i=54863:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_397:95149_awrs=decay:awrsf=30:s2a=on:urr=on:i=34407:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1024_afp=1000:avsq=on:awrs=converge:bd=preordered:drc=off:ins=1:ss=axioms:st=5.0:to=lpo:uwa=interpreted_only:i=144525:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_74417:511564_awrs=decay:awrsf=2:bd=off:bs=on:drc=off:lwlo=on:spb=goal_then_units:i=93175:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_fde=unused:nwc=10.0:s2a=on:s2at=3.0:sac=on:i=108631:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1527:478415_awrs=decay:awrsf=4:drc=off:foolp=on:to=lpo:i=64901:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:64_bd=preordered:nwc=5.0:to=lpo:uwa=one_side_interpreted:i=32754:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:4_av=off:bd=off:drc=off:ins=1:nwc=2.0:spb=goal:tgt=full:to=lpo:i=37361:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=299577:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:128_drc=off:ins=1:sp=const_frequency:tgt=ground:i=10938:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:14_awrs=converge:sp=unary_first:tgt=ground:i=21074:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:br=off:sas=z3:spb=goal:tgt=full:tha=some:to=lpo:uwa=all:i=79318:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bsr=unit_only:cond=on:flr=on:newcnf=on:nwc=10.0:sas=z3:to=lpo:i=6132:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_drc=off:sos=all:sp=unary_first:tgt=full:urr=ec_only:i=47137:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:128_aac=none:acc=on:amm=off:atotf=0.1:bd=preordered:drc=off:fd=preordered:fde=none:gs=on:nicw=on:s2a=on:s2at=5.0:slsq=on:sp=const_max:spb=non_intro:tgt=ground:to=lpo:i=108833:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:5_bs=unit_only:drc=off:ins=1:nwc=2.16:rnwc=on:slsq=on:slsqr=13,149:sp=const_min:tgt=ground:to=lpo:uwa=interpreted_only:i=120001:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sos=all:ss=axioms:st=5.0:i=21624:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_av=off:sp=frequency:updr=off:urr=ec_only:i=23755:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_ep=R:sd=2:sos=on:ss=axioms:i=5794:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=1:ss=axioms:st=5.0:urr=on:i=5101:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:i=242013:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:16_add=large:anc=none:bce=on:bs=on:gs=on:nwc=6.0:sp=occurrence:updr=off:i=14229:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:16_awrs=decay:awrsf=260:bsr=on:er=known:gsp=on:newcnf=on:nwc=3.0:s2a=on:sas=z3:sd=4:ss=axioms:i=18702:si=on:rawr=on:rtra=on_0");
    quick.push("dis+2_1:1_av=off:lcm=predicate:nm=2:sd=2:sos=on:sp=const_min:ss=axioms:st=1.5:i=68603:si=on:rawr=on:rtra=on_0");
    quick.push("ott-3_2:1_acc=on:add=large:anc=none:fde=none:gsp=on:irw=on:nm=0:s2a=on:sd=4:sos=on:ss=axioms:st=1.2:urr=on:i=76460:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_acc=on:urr=ec_only:i=33643:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_av=off:gsp=on:lcm=predicate:newcnf=on:nm=2:sd=3:sos=on:ss=axioms:i=13392:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_bd=off:sd=2:sos=all:sp=unary_frequency:ss=axioms:i=29131:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_av=off:gs=on:gsp=on:irw=on:nwc=2.0:sd=2:sos=on:ss=axioms:stl=30:urr=on:i=28205:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_1:1_aac=none:acc=on:add=large:bd=off:bs=unit_only:bsr=on:cond=on:nm=0:sac=on:sd=3:sos=on:ss=axioms:st=2.0:i=194315:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_anc=all:ep=RST:fde=unused:fsr=off:gsp=on:nm=16:sd=2:sos=on:ss=axioms:st=5.0:i=6215:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:5_acc=on:afp=1010:fsr=off:gsp=on:nm=10:sac=on:sos=on:sp=unary_first:urr=ec_only:i=69362:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bd=off:fd=preordered:fde=unused:rp=on:sfv=off:sos=on:sp=reverse_frequency:spb=goal:to=lpo:i=2412:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:rp=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=283298:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:rp=on:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=432558:si=on:rawr=on:rtra=on_0");
    quick.push("ott+4_1:28_av=off:sos=all:i=59416:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_8:1_afp=100000:afq=2.0:anc=all_dependent:bd=off:gs=on:gsp=on:lwlo=on:nicw=on:nwc=3.0:sac=on:stl=30:i=29538:si=on:rawr=on:rtra=on_0");
    quick.push("dis+2_1:64_add=large:bce=on:bd=off:i=53182:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:10_bd=off:sac=on:sas=z3:sos=on:i=224012:si=on:rawr=on:rtra=on_0");
    // Improves by expected 20.526961111917363 probs costing 3969706 Mi
    // Overall score 6818.525478979261 probs on average / budget 14725172 Mi
  } else {
    // problemsCNFrestUNS.txt
    // Champion singleton-schedule for 100000Mi
    quick.push("lrs+10_1:1_kws=precedence:lwlo=on:tgt=ground:i=99966:si=on:rawr=on:rtra=on_0");
    // Improves by expected 3672.88796264065 probs costing 99965 Mi
    // Sub-schedule for 50Mi strat cap / 400Mi overall limit
    quick.push("dis+21_1:1_av=off:fd=off:lcm=predicate:sos=on:spb=goal:urr=ec_only:i=42:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:16_awrs=converge:awrsf=40:br=off:ep=RSTC:flr=on:gsp=on:nwc=3.0:sos=on:urr=on:i=4:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bd=off:drc=off:lcm=reverse:nwc=5.0:sd=1:sgt=16:spb=goal_then_units:ss=axioms:to=lpo:i=43:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_5:1_br=off:fde=none:nwc=3.0:sd=1:sgt=10:sos=on:ss=axioms:urr=on:i=34:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:16_fsr=off:nwc=2.0:i=25:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_av=off:er=filter:slsq=on:slsqc=0:slsqr=1,1:sp=frequency:to=lpo:i=49:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:4_amm=off:bce=on:sd=1:sos=on:ss=included:i=51:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_atotf=0.0306256:ep=RST:mep=off:nm=0:sos=all:i=3:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:fd=off:fde=none:ins=3:sac=on:sos=on:spb=goal:to=lpo:i=51:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1004_1:734_av=off:awrs=converge:awrsf=70:br=off:ep=RSTC:erd=off:gs=on:nwc=3.0:s2a=on:s2agt=16:sp=occurrence:updr=off:urr=on:i=6:si=on:rawr=on:rtra=on_0");
    quick.push("dis+4_1:1_bd=off:cond=fast:fde=unused:lcm=reverse:lma=on:nicw=on:nwc=2.0:s2a=on:s2agt=16:sac=on:sp=frequency:i=23:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_drc=off:sp=reverse_frequency:spb=goal:to=lpo:i=5:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+30_1:12_av=off:bs=unit_only:fsd=on:gs=on:lwlo=on:newcnf=on:slsq=on:slsqr=1,2:i=3:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_3:29_av=off:awrs=decay:awrsf=32:bce=on:drc=off:fde=unused:gsp=on:irw=on:nwc=2.0:spb=goal_then_units:updr=off:urr=ec_only:i=29:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_fmbes=contour:fmbsr=2.0:fmbsso=input_usage:i=6:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_1:1_aac=none:add=large:anc=all_dependent:cond=fast:ep=RST:fsr=off:lma=on:nm=2:sos=on:sp=reverse_arity:stl=30:uhcvi=on:urr=on:i=2:si=on:rawr=on:rtra=on_0");
    quick.push("ott+2_1:64_afp=40000:bd=off:irw=on:i=8:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1003_1:1024_add=large:afr=on:cond=fast:fsr=off:gs=on:sos=on:sp=reverse_arity:i=28:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_afp=100000:afr=on:amm=sco:bd=preordered:cond=fast:newcnf=on:nm=4:sos=on:sp=occurrence:i=7:si=on:rawr=on:rtra=on_0");
    // Improves by expected 167.29832899060656 probs costing 400 Mi
    // Sub-schedule for 100Mi strat cap / 800Mi overall limit
    quick.push("lrs+10_1:7_av=off:awrs=converge:awrsf=40:br=off:bsd=on:cond=on:drc=off:nwc=3.0:plsq=on:plsqc=1:s2a=on:s2agt=16:to=lpo:urr=on:i=6:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:fsr=off:sd=1:sos=on:ss=axioms:i=67:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_1:1_erd=off:s2a=on:sac=on:sd=1:sgt=64:sos=on:ss=included:st=3.0:to=lpo:urr=on:i=97:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_aac=none:bsr=unit_only:ep=R:sac=on:sos=all:i=37:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_add=large:alpa=false:anc=none:fd=off:lcm=reverse:nwc=5.0:sd=2:sgt=20:ss=included:i=46:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:16_acc=on:anc=all:avsq=on:awrs=converge:s2a=on:sac=on:sos=on:ss=axioms:i=81:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+3_8:1_anc=none:erd=off:fsd=on:s2a=on:s2agt=16:sgt=16:sos=on:sp=frequency:ss=included:i=71:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:sd=2:sos=on:sp=reverse_arity:ss=axioms:to=lpo:i=73:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sos=all:ss=axioms:st=1.5:i=20:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:fd=off:fde=none:ins=3:sac=on:sos=on:spb=goal:to=lpo:i=100:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_br=off:ep=RSTC:sos=all:urr=on:i=14:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+4_1:1_fde=unused:sos=on:i=39:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+30_1:12_av=off:bs=unit_only:fsd=on:gs=on:lwlo=on:newcnf=on:slsq=on:slsqr=1,2:i=3:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bd=off:canc=force:ev=cautious:nwc=5.0:i=33:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:2_av=off:bd=off:fd=off:lcm=predicate:nwc=10.0:s2a=on:s2at=2.0:sp=reverse_arity:spb=goal:i=29:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:32_av=off:awrs=decay:awrsf=16:bs=on:fsr=off:gs=on:gsp=on:nwc=1.4:s2a=on:s2agt=32:urr=on:i=34:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:8_aac=none:bs=unit_only:er=filter:fd=off:nwc=5.0:s2pl=no:i=46:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_fde=unused:fmbsr=1.78:fmbsso=preprocessed_usage:gsp=on:ins=1:newcnf=on:updr=off:i=22:si=on:rawr=on:rtra=on_0");
    // Improves by expected 65.49608605006348 probs costing 800 Mi
    // Sub-schedule for 150Mi strat cap / 1200Mi overall limit
    quick.push("dis+1011_1:1_av=off:er=known:fde=unused:nwc=10.0:slsq=on:slsqc=1:slsqr=4,15:i=75:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:16_awrs=converge:awrsf=40:br=off:ep=RSTC:flr=on:gsp=on:nwc=3.0:sos=on:urr=on:i=7:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_1:1_erd=off:s2a=on:sac=on:sd=1:sgt=64:sos=on:ss=included:st=3.0:to=lpo:urr=on:i=151:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:64_nwc=3.0:s2a=on:sd=1:sgt=64:ss=included:i=37:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_av=off:er=filter:slsq=on:slsqc=0:slsqr=1,1:sp=frequency:to=lpo:i=147:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:7_av=off:bsr=on:fd=preordered:nwc=5.0:s2a=on:s2at=2.0:sp=reverse_frequency:to=lpo:urr=on:i=45:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=RS:flr=on:nm=2:sos=on:i=109:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:fd=off:fde=none:ins=3:sac=on:sos=on:spb=goal:to=lpo:i=151:si=on:rawr=on:rtra=on_0");
    quick.push("dis+4_1:1_bd=off:cond=fast:fde=unused:lcm=reverse:lma=on:nicw=on:nwc=2.0:s2a=on:s2agt=16:sac=on:sp=frequency:i=116:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_drc=off:sp=reverse_frequency:spb=goal:to=lpo:i=7:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_aac=none:drc=off:fsr=off:nwc=2.0:sp=occurrence:ss=included:i=149:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:1_drc=off:sp=reverse_frequency:spb=goal_then_units:to=lpo:i=57:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:6_av=off:bce=on:ins=1:nwc=2.0:tgt=ground:thsq=on:thsqc=32:updr=off:i=69:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_atotf=0.3:fsr=off:nwc=5.0:s2a=on:s2at=5.0:slsq=on:slsqc=1:slsqr=3,2:i=92:si=on:rawr=on:rtra=on_0");
    // Improves by expected 42.88894074745989 probs costing 1198 Mi
    // Sub-schedule for 500Mi strat cap / 4000Mi overall limit
    quick.push("lrs+1010_1:1_aac=none:bce=on:nicw=on:nm=0:plsq=on:plsql=on:sac=on:sos=on:sp=frequency:spb=units:to=lpo:i=307:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_sgt=16:sos=on:spb=goal:ss=axioms:i=137:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_av=off:fd=off:lcm=predicate:sos=on:spb=goal:urr=ec_only:i=108:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_1:1_erd=off:s2a=on:sac=on:sd=1:sgt=64:sos=on:ss=included:st=3.0:to=lpo:urr=on:i=278:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_br=off:plsq=on:plsqr=32,1:slsq=on:slsqc=1:slsqr=1,1:sp=frequency:to=lpo:urr=ec_only:i=500:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1010_1:1_acc=on:bd=off:br=off:bsr=on:drc=off:erd=off:nicw=on:sac=on:sos=on:to=lpo:urr=on:i=143:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_2:3_anc=all:br=off:fsr=off:nwc=5.0:s2a=on:s2agt=10:urr=on:i=490:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_awrs=converge:awrsf=20:drc=off:fd=preordered:slsq=on:slsqc=0:slsqr=1,2:sos=on:to=lpo:i=78:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=RS:flr=on:nm=2:sos=on:i=95:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_2:1_abs=on:fde=none:lcm=reverse:nwc=2.0:plsq=on:plsqc=1:plsql=on:plsqr=4095,256:s2a=on:sac=on:sp=reverse_arity:i=156:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_1:1_bd=off:bsr=unit_only:drc=off:fd=preordered:fsr=off:nwc=3.0:sac=on:to=lpo:urr=on:i=240:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:4_av=off:bs=unit_only:bsr=unit_only:ep=RS:s2a=on:sos=on:sp=frequency:to=lpo:i=119:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_amm=off:drc=off:sp=reverse_frequency:spb=goal_then_units:to=lpo:i=141:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_av=off:bce=on:bd=off:bsr=unit_only:flr=on:gs=on:nwc=2.0:rnwc=on:sp=frequency:thsq=on:thsqc=64:thsqd=1:thsql=off:to=lpo:i=298:si=on:rawr=on:rtra=on_0");
    quick.push("dis+22_1:128_bsd=on:slsq=on:slsqc=1:slsqr=1,6:sp=frequency:spb=goal:thsq=on:thsqc=16:thsqd=1:thsql=off:i=58:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+4_1:1_fde=unused:sos=on:i=39:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1003_1:128_av=off:nwc=5.0:s2a=on:sp=unary_frequency:tgt=full:to=lpo:i=378:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:8_aac=none:bs=unit_only:er=filter:fd=off:nwc=5.0:s2pl=no:i=46:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1010_4:1_bsr=unit_only:fde=unused:nwc=10.0:s2a=on:s2agt=32:slsq=on:slsqc=2:thsq=on:thsqc=64:thsqd=16:i=171:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_aac=none:abs=on:add=off:ep=RS:flr=on:fsr=off:lcm=reverse:lma=on:nicw=on:nwc=3.0:sos=all:i=182:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1024_drc=off:ins=1:nwc=5.0:slsq=on:slsqc=1:slsql=off:slsqr=1,8:urr=on:uwa=all:i=40:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_fmbes=contour:i=7:si=on:rawr=on:rtra=on_0");
    // Improves by expected 74.01703478670106 probs costing 3989 Mi
    // Sub-schedule for 1000Mi strat cap / 8000Mi overall limit
    quick.push("dis+1011_1:1_av=off:er=known:fde=unused:nwc=10.0:slsq=on:slsqc=1:slsqr=4,15:i=106:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_acc=on:avsq=on:avsqc=2:avsqr=1,16:drc=off:nwc=5.0:sd=1:ss=included:st=4.0:urr=on:i=70:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_aac=none:lcm=reverse:nwc=10.0:sos=on:ss=axioms:st=3.0:i=101:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_5:1_br=off:fde=none:nwc=3.0:sd=1:sgt=10:sos=on:ss=axioms:urr=on:i=162:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_nwc=2.0:spb=goal_then_units:ss=axioms:st=5.0:i=45:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_90:23_awrs=decay:awrsf=16:bce=on:cond=on:drc=off:fd=preordered:fde=unused:flr=on:gs=on:sp=frequency:urr=on:i=389:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_5:1_bce=on:bd=off:bsr=unit_only:s2a=on:sos=all:sp=reverse_arity:ss=axioms:st=2.0:to=lpo:urr=on:i=226:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:1_lcm=predicate:sos=on:sp=frequency:i=272:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_av=off:er=filter:slsq=on:slsqc=0:slsqr=1,1:sp=frequency:to=lpo:i=654:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:4_amm=off:bce=on:sd=1:sos=on:ss=included:i=85:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_atotf=0.0306256:ep=RST:mep=off:nm=0:sos=all:i=15:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:1_av=off:newcnf=on:nwc=5.0:rnwc=on:slsq=on:slsqc=0:slsqr=1,1:spb=goal_then_units:to=lpo:i=156:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+3_1:1_br=off:bsr=on:cond=on:ep=RS:etr=on:flr=on:gs=on:gsem=on:gsp=on:ins=2:lcm=predicate:lwlo=on:plsq=on:plsqr=36625,677197:sims=off:slsq=on:slsqc=0:slsqr=171,238:sos=theory:sp=weighted_frequency:spb=goal:urr=on:i=141:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_av=off:bd=off:bsr=unit_only:erd=off:etr=on:nm=0:sfv=off:sos=on:i=185:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_flr=on:s2a=on:sp=occurrence:urr=on:i=86:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:4_awrs=converge:sp=frequency:to=lpo:i=344:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1024_cond=fast:i=104:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1003_1:1_ep=R:erd=off:sos=on:urr=on:i=355:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bd=off:canc=force:ev=cautious:nwc=5.0:i=29:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_atotf=0.3:fsr=off:nwc=5.0:s2a=on:s2at=5.0:slsq=on:slsqc=1:slsqr=3,2:i=92:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_2:3_av=off:fde=unused:nwc=5.0:tgt=ground:i=460:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+31_1:1_fs=off:fsr=off:kws=precedence:i=498:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_fd=preordered:tgt=ground:i=274:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:4_av=off:bd=off:br=off:fsr=off:plsq=on:plsqr=20,11:s2a=on:urr=ec_only:i=1000:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_av=off:bsr=unit_only:drc=off:plsq=on:slsq=on:slsqc=1:slsqr=1,2:i=310:si=on:rawr=on:rtra=on_0");
    quick.push("dis+34_1:32_abs=on:add=off:bsr=on:gsp=on:sp=weighted_frequency:i=174:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+31_1:1_bs=on:bsr=on:fsr=off:gs=on:gsp=on:sp=weighted_frequency:spb=units:to=lpo:i=298:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_br=off:bsr=on:fsr=off:nwc=2.0:s2a=on:s2agt=12:s2at=5.0:urr=on:i=874:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ep=RST:sd=2:sos=on:ss=axioms:st=5.0:i=151:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:5_er=filter:nwc=6.0:sd=2:sos=on:ss=axioms:st=1.5:i=75:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=1:sos=on:ss=axioms:st=5.0:i=184:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:128_aac=none:avsq=on:avsqc=1:avsql=on:awrs=converge:flr=on:nwc=4.0:plsq=on:plsqc=2:plsql=on:plsqr=1,32:rp=on:sac=on:slsq=on:slsqc=2:slsql=off:slsqr=1,2:sp=occurrence:i=24:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_981:877462_av=off:awrs=decay:awrsf=1:bd=off:er=filter:erd=off:etr=on:fd=off:fsd=on:gs=on:gsp=on:nwc=5.0:plsq=on:plsqc=2:plsqr=371,20:rp=on:slsq=on:slsqc=1:slsql=off:slsqr=19,32:sp=occurrence:thsq=on:thsqc=16:thsqd=32:thsqr=239,12:i=87:si=on:rawr=on:rtra=on_0");
    // Improves by expected 57.10226703351513 probs costing 7993 Mi
    // Sub-schedule for 1500Mi strat cap / 12000Mi overall limit
    quick.push("lrs+10_1:1_acc=on:avsq=on:avsqc=2:avsqr=1,16:drc=off:nwc=5.0:sd=1:ss=included:st=4.0:urr=on:i=374:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_drc=off:flr=on:nwc=2.0:sac=on:urr=ec_only:i=1220:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:bd=preordered:bs=unit_only:slsq=on:slsqc=0:slsqr=1,1:sos=on:sp=frequency:spb=goal_then_units:to=lpo:urr=ec_only:i=696:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:16_awrs=converge:awrsf=40:br=off:ep=RSTC:flr=on:gsp=on:nwc=3.0:sos=on:urr=on:i=181:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_br=off:plsq=on:plsqr=32,1:slsq=on:slsqc=1:slsqr=1,1:sp=frequency:to=lpo:urr=ec_only:i=794:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:2_br=off:bs=unit_only:bsr=unit_only:nwc=5.0:s2a=on:s2agt=32:urr=on:i=368:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_bs=unit_only:flr=on:gs=on:nicw=on:nwc=2.0:s2a=on:sac=on:sas=z3:ss=axioms:st=2.6:updr=off:i=1065:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:16_acc=on:anc=all:avsq=on:awrs=converge:s2a=on:sac=on:sos=on:ss=axioms:i=51:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:128_afr=on:amm=sco:bd=off:cond=fast:nm=0:nwc=2.0:rnwc=on:s2a=on:s2at=1.5:slsq=on:slsqc=0:slsqr=1,8:sos=on:sp=reverse_arity:i=381:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_bd=off:br=off:drc=off:to=lpo:urr=ec_only:i=167:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:8_drc=off:fd=preordered:fde=unused:sp=reverse_frequency:ss=axioms:st=2.0:i=107:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_bd=preordered:nwc=2.0:sp=reverse_arity:to=lpo:urr=on:i=108:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:32_av=off:fde=unused:lcm=reverse:s2a=on:s2at=5.0:i=127:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:8_aac=none:abs=on:anc=all_dependent:bd=off:bsr=on:cond=on:fde=unused:fsr=off:sos=on:ss=axioms:i=74:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=RS:flr=on:nm=2:sos=on:i=64:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:fd=off:fde=none:ins=3:sac=on:sos=on:spb=goal:to=lpo:i=885:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_2:1_abs=on:fde=none:lcm=reverse:nwc=2.0:plsq=on:plsqc=1:plsql=on:plsqr=4095,256:s2a=on:sac=on:sp=reverse_arity:i=610:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_flr=on:s2a=on:sp=occurrence:urr=on:i=86:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+22_1:4_alpa=false:avsq=on:fsr=off:nwc=3.0:sos=all:uwa=ground:i=260:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+33_1:1_av=off:bsr=unit_only:flr=on:lcm=predicate:sp=frequency:i=1496:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_acc=model:avsq=on:bd=off:flr=on:fsd=on:gs=on:newcnf=on:plsq=on:plsql=on:plsqr=1,32:s2a=on:s2at=3.0:sac=on:skr=on:sos=on:sp=occurrence:updr=off:i=56:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_asg=force:av=off:bsr=on:cond=fast:dr=on:drc=off:er=known:fde=unused:foolp=on:inw=on:nm=4:norm_ineq=on:nwc=4.0:s2a=on:sfv=off:skr=on:sp=reverse_arity:tac=rule:to=lpo:urr=on:i=266:si=on:rawr=on:rtra=on_0");
    quick.push("dis+22_1:20_av=off:bd=off:fde=unused:plsq=on:slsq=on:uwa=all:i=191:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:6_av=off:bce=on:ins=1:nwc=2.0:tgt=ground:thsq=on:thsqc=32:updr=off:i=76:si=on:rawr=on:rtra=on_0");
    quick.push("ott+4_1:5_av=off:bce=on:erd=off:fd=preordered:flr=on:fsr=off:gsp=on:nwc=3.0:plsq=on:rnwc=on:tgt=ground:urr=on:i=590:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1003_1:8_av=off:bd=off:bs=unit_only:nwc=10.0:plsq=on:plsql=on:plsqr=63,64:tgt=full:i=457:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_atotf=0.3:fsr=off:nwc=5.0:s2a=on:s2at=5.0:slsq=on:slsqc=1:slsqr=3,2:i=94:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_drc=off:s2a=on:s2agt=8:sp=reverse_arity:to=lpo:i=201:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_4:1_drc=off:ins=1:plsq=on:plsqc=1:plsqr=1,8:s2at=2.0:s2pl=on:slsq=on:slsqc=1:slsql=off:sp=unary_first:tgt=full:i=98:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:4_av=off:bd=off:fde=unused:lcm=predicate:nwc=1.5:sp=const_frequency:i=253:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_1:1_sd=1:sos=on:ss=axioms:st=3.0:i=281:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:128_aac=none:avsq=on:avsqc=1:avsql=on:awrs=converge:flr=on:nwc=4.0:plsq=on:plsqc=2:plsql=on:plsqr=1,32:rp=on:sac=on:slsq=on:slsqc=2:slsql=off:slsqr=1,2:sp=occurrence:i=24:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_39044:804583_anc=all:avsq=on:avsqr=302,909:awrs=decay:awrsf=20:bd=off:bsr=on:cond=on:gsp=on:nm=0:nwc=2.0:plsq=on:plsqr=9,13:rp=on:s2a=on:s2agt=16:sac=on:thsq=on:thsqc=32:thsqd=32:thsql=off:to=lpo:updr=off:uwa=all:i=321:si=on:rawr=on:rtra=on_0");
    // Improves by expected 47.95882526392416 probs costing 11989 Mi
    // Sub-schedule for 5000Mi strat cap / 40000Mi overall limit
    quick.push("lrs+1010_1:1_aac=none:bce=on:nicw=on:nm=0:plsq=on:plsql=on:sac=on:sos=on:sp=frequency:spb=units:to=lpo:i=788:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:7_av=off:awrs=converge:awrsf=40:br=off:bsd=on:cond=on:drc=off:nwc=3.0:plsq=on:plsqc=1:s2a=on:s2agt=16:to=lpo:urr=on:i=2378:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_avsq=on:avsqc=2:avsql=on:avsqr=1,16:nwc=5.0:sac=on:spb=units:i=1730:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:1_av=off:flr=on:ins=1:sos=on:sp=reverse_frequency:ss=axioms:urr=on:i=246:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bd=off:drc=off:lcm=reverse:nwc=5.0:sd=1:sgt=16:spb=goal_then_units:ss=axioms:to=lpo:i=74:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1010_1:1_acc=on:bd=off:br=off:bsr=on:drc=off:erd=off:nicw=on:sac=on:sos=on:to=lpo:urr=on:i=3168:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:16_acc=on:anc=all:avsq=on:awrs=converge:s2a=on:sac=on:sos=on:ss=axioms:i=91:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:8_bd=off:br=off:s2a=on:s2at=3.0:urr=ec_only:i=1096:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:64_nwc=3.0:s2a=on:sd=1:sgt=64:ss=included:i=617:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_nwc=2.0:spb=goal_then_units:ss=axioms:st=5.0:i=53:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_acc=on:br=off:nwc=10.0:s2a=on:s2agt=64:sac=on:urr=on:i=467:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_1:7_bd=off:i=4430:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:128_av=off:fd=preordered:flr=on:gsp=on:ins=1:urr=on:i=1838:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:8_drc=off:fd=preordered:fde=unused:sp=reverse_frequency:ss=axioms:st=2.0:i=107:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_bd=preordered:nwc=2.0:sp=reverse_arity:to=lpo:urr=on:i=108:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_av=off:er=filter:slsq=on:slsqc=0:slsqr=1,1:sp=frequency:to=lpo:i=208:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=RS:flr=on:nm=2:sos=on:i=64:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_flr=on:s2a=on:sp=occurrence:urr=on:i=86:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_av=off:br=off:fd=preordered:fs=off:fsr=off:ins=2:sp=reverse_frequency:to=lpo:urr=ec_only:i=508:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:128_br=off:plsq=on:plsqr=32,1:urr=ec_only:i=2344:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_acc=model:avsq=on:bd=off:flr=on:fsd=on:gs=on:newcnf=on:plsq=on:plsql=on:plsqr=1,32:s2a=on:s2at=3.0:sac=on:skr=on:sos=on:sp=occurrence:updr=off:i=56:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+33_1:16_avsq=on:avsqr=23,8:plsq=on:plsqc=1:plsql=on:plsqr=4,1:sac=on:sas=z3:sp=frequency:to=lpo:urr=ec_only:i=1385:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:32_av=off:drc=off:lma=on:plsq=on:plsqc=2:plsqr=32,1:sp=frequency:to=lpo:i=505:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+30_1:32_avsq=on:avsql=on:ep=RS:ins=1:nwc=10.0:s2a=on:sd=1:sgt=16:sp=frequency:ss=included:urr=on:uwa=one_side_interpreted:i=314:si=on:rawr=on:rtra=on_0");
    quick.push("dis+22_1:20_av=off:bd=off:fde=unused:plsq=on:slsq=on:uwa=all:i=1408:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:16_fsr=off:nwc=3.0:plsq=on:plsqc=1:slsq=on:slsqc=2:sp=occurrence:i=457:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:6_av=off:bce=on:ins=1:nwc=2.0:tgt=ground:thsq=on:thsqc=32:updr=off:i=76:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_4:3_av=off:awrs=converge:awrsf=16:bce=on:bsr=unit_only:cond=on:er=known:flr=on:irw=on:newcnf=on:nwc=1.9:rnwc=on:s2a=on:s2agt=32:s2at=3.2:slsq=on:slsqc=1:slsqr=1,4:sp=reverse_arity:spb=intro:thsq=on:thsqc=64:thsqd=16:thsql=off:updr=off:i=381:si=on:rawr=on:rtra=on_0");
    quick.push("dis+33_1:1_av=off:bd=off:gsp=on:slsq=on:slsqr=1,4:sp=const_min:tgt=ground:i=162:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:16_bd=preordered:drc=off:s2a=on:tgt=ground:i=163:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:32_av=off:awrs=decay:awrsf=16:bs=on:fsr=off:gs=on:gsp=on:nwc=1.4:s2a=on:s2agt=32:urr=on:i=297:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bd=preordered:drc=off:sp=frequency:to=lpo:urr=on:i=1393:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:4_av=off:bd=off:br=off:fsr=off:plsq=on:plsqr=20,11:s2a=on:urr=ec_only:i=1907:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:drc=off:slsq=on:slsqc=1:slsqr=29,16:sp=reverse_frequency:to=lpo:i=799:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_aac=none:abs=on:add=off:ep=RS:flr=on:fsr=off:lcm=reverse:lma=on:nicw=on:nwc=3.0:sos=all:i=179:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+31_1:1_bs=on:bsr=on:fsr=off:gs=on:gsp=on:sp=weighted_frequency:spb=units:to=lpo:i=874:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_i=4546:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_4:1_drc=off:ins=1:plsq=on:plsqc=1:plsqr=1,8:s2at=2.0:s2pl=on:slsq=on:slsqc=1:slsql=off:sp=unary_first:tgt=full:i=98:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:64_bd=off:lcm=predicate:sac=on:sp=const_frequency:urr=on:i=2492:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ep=RST:sd=2:sos=on:ss=axioms:st=5.0:i=123:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:5_er=filter:nwc=6.0:sd=2:sos=on:ss=axioms:st=1.5:i=89:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=1:sos=on:ss=axioms:st=5.0:i=191:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_1:1_sd=1:sos=on:ss=axioms:st=3.0:i=506:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:rp=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=389:si=on:rawr=on:rtra=on_0");
    // Improves by expected 84.21102808719691 probs costing 39998 Mi
    // Sub-schedule for 10000Mi strat cap / 80000Mi overall limit
    quick.push("lrs+10_1:1_aac=none:bd=off:plsq=on:plsqc=1:plsqr=32,1:sfv=off:sos=all:sp=reverse_arity:i=1282:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_acc=on:avsq=on:avsqc=2:avsqr=1,16:drc=off:nwc=5.0:sd=1:ss=included:st=4.0:urr=on:i=206:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_339093:436673_av=off:awrs=decay:awrsf=2:bce=on:bsr=on:drc=off:flr=on:newcnf=on:plsq=on:plsql=on:plsqr=1,2:sp=frequency:spb=units:to=lpo:urr=on:i=951:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_avsq=on:avsqc=2:avsql=on:avsqr=1,16:nwc=5.0:sac=on:spb=units:i=367:si=on:rawr=on:rtra=on_0");
    quick.push("ott+21_1:1_erd=off:s2a=on:sac=on:sd=1:sgt=64:sos=on:ss=included:st=3.0:to=lpo:urr=on:i=222:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_br=off:plsq=on:plsqr=32,1:slsq=on:slsqc=1:slsqr=1,1:sp=frequency:to=lpo:urr=ec_only:i=1186:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_atotf=0.1:lcm=predicate:nwc=5.0:rnwc=on:s2a=on:s2at=2.0:sac=on:sos=on:spb=goal_then_units:urr=on:i=1038:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bd=off:drc=off:lcm=reverse:nwc=5.0:sd=1:sgt=16:spb=goal_then_units:ss=axioms:to=lpo:i=74:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1003_1:1_aac=none:amm=off:ep=R:erd=off:newcnf=on:sac=on:skr=on:sos=all:i=1257:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:16_av=off:flr=on:nwc=5.0:s2a=on:sos=on:urr=on:i=2967:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:3_bd=preordered:drc=off:erd=off:flr=on:lwlo=on:s2a=on:s2at=3.0:sp=reverse_arity:ss=included:to=lpo:urr=on:i=1932:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1004_4:1_bd=off:sd=1:sims=off:skr=on:sos=all:ss=axioms:st=2.0:i=341:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:4_aac=none:avsq=on:avsqc=1:avsqr=2047,512:cond=fast:drc=off:nwc=3.0:plsq=on:plsqc=2:plsqr=3,2:sac=on:sas=z3:spb=goal:i=1100:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:8_bd=off:br=off:s2a=on:s2at=3.0:urr=ec_only:i=3814:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1_1:64_awrs=converge:bd=off:flr=on:sd=1:ss=axioms:st=1.5:to=lpo:i=3452:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1002_1221:202_aac=none:anc=all:awrs=decay:bce=on:ep=R:gsp=on:nwc=5.0:s2a=on:s2agt=23:sac=on:urr=on:i=1737:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:8_drc=off:fd=preordered:fde=unused:sp=reverse_frequency:ss=axioms:st=2.0:i=107:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_fde=none:slsq=on:slsqc=0:slsqr=1,1:i=979:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_av=off:bce=on:br=off:drc=off:fsr=off:slsq=on:slsqc=2:slsql=off:slsqr=7,25:sp=frequency:ss=included:st=5.0:to=lpo:urr=ec_only:i=1178:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_bd=preordered:nwc=2.0:sp=reverse_arity:to=lpo:urr=on:i=108:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_av=off:er=filter:slsq=on:slsqc=0:slsqr=1,1:sp=frequency:to=lpo:i=654:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=RS:flr=on:nm=2:sos=on:i=265:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_flr=on:s2a=on:sp=occurrence:urr=on:i=67:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:8_awrs=decay:awrsf=4:drc=off:ins=3:sp=occurrence:ss=axioms:i=2055:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:64_anc=all:awrs=converge:drc=off:nicw=on:nwc=3.0:s2a=on:sac=on:spb=goal_then_units:i=336:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+4_1:1_av=off:bd=off:lwlo=on:nwc=5.0:s2a=on:s2at=2.0:slsq=on:slsqc=2:slsql=off:slsqr=1,2:sp=frequency:i=3439:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_aac=none:drc=off:fsr=off:nwc=2.0:sp=occurrence:ss=included:i=179:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_acc=model:avsq=on:bd=off:flr=on:fsd=on:gs=on:newcnf=on:plsq=on:plsql=on:plsqr=1,32:s2a=on:s2at=3.0:sac=on:skr=on:sos=on:sp=occurrence:updr=off:i=56:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1003_1:128_av=off:nwc=5.0:s2a=on:sp=unary_frequency:tgt=full:to=lpo:i=2303:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:14_awrs=converge:br=off:drc=off:ev=cautious:s2a=on:sfv=off:tgt=ground:tha=off:urr=on:i=1449:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=4882:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_atotf=0.3:fsr=off:nwc=5.0:s2a=on:s2at=5.0:slsq=on:slsqc=1:slsqr=3,2:i=94:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:12_abs=on:avsq=on:avsqr=5,31:bd=off:bsr=unit_only:plsq=on:plsql=on:plsqr=1,32:sac=on:sas=z3:spb=goal_then_units:tgt=full:to=lpo:i=9837:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_2:3_av=off:fde=unused:nwc=5.0:tgt=ground:i=1949:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+31_1:1_fs=off:fsr=off:kws=precedence:i=761:si=on:rawr=on:rtra=on_0");
    quick.push("dis+2_1:14_bs=on:cond=on:lcm=reverse:sac=on:i=893:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:16_acc=on:drc=off:fd=preordered:fsd=on:nwc=2.0:slsq=on:slsqc=2:slsql=off:slsqr=1,16:thsq=on:thsqc=16:thsqd=16:urr=on:i=9168:si=on:rawr=on:rtra=on_0");
    quick.push("dis+20_1:20_av=off:awrs=converge:bs=on:fsr=off:nwc=3.0:urr=ec_only:i=1819:si=on:rawr=on:rtra=on_0");
    quick.push("ott+0_1:1_av=off:bsr=unit_only:gsp=on:s2a=on:s2at=2.0:sos=on:i=2891:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:1_aac=none:abs=on:add=off:ep=RS:flr=on:fsr=off:lcm=reverse:lma=on:nicw=on:nwc=3.0:sos=all:i=179:si=on:rawr=on:rtra=on_0");
    quick.push("dis+35_1:5_av=off:s2a=on:slsq=on:slsqc=1:slsqr=1,4:sp=const_frequency:updr=off:i=1249:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_av=off:bd=off:bs=unit_only:drc=off:etr=on:fd=preordered:flr=on:ins=2:nwc=10.0:s2a=on:s2at=1.18:sims=off:sp=reverse_arity:to=lpo:i=1470:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+31_160:31_acc=on:anc=all_dependent:awrs=decay:awrsf=32:sac=on:sd=1:sos=on:ss=axioms:st=2.0:to=lpo:i=177:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:1_av=off:drc=off:fd=preordered:foolp=on:ins=1:kws=inv_arity:plsq=on:plsqc=1:plsqr=3,25:s2at=2.0:slsq=on:slsqc=1:slsql=off:slsqr=1,8:sp=unary_frequency:urr=ec_only:uwa=one_side_interpreted:i=663:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_4:1_drc=off:ins=1:plsq=on:plsqc=1:plsqr=1,8:s2at=2.0:s2pl=on:slsq=on:slsqc=1:slsql=off:sp=unary_first:tgt=full:i=98:si=on:rawr=on:rtra=on_0");
    quick.push("dis+3_4:1_aac=none:anc=none:bd=off:cond=fast:er=known:fd=off:fde=unused:fsr=off:lcm=reverse:nicw=on:nwc=3.0:rnwc=on:sp=frequency:tgt=full:urr=ec_only:i=2707:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ep=RST:sd=2:sos=on:ss=axioms:st=5.0:i=123:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_sas=z3:sd=1:sos=all:ss=axioms:st=3.0:i=702:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=3:sos=on:ss=axioms:st=2.0:i=1607:si=on:rawr=on:rtra=on_0");
    quick.push("dis+2_1:16_fsr=off:lcm=reverse:lma=on:i=784:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=1:sos=on:ss=axioms:st=5.0:i=86:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1010_1:1024_av=off:bd=off:br=off:sd=1:sp=const_min:ss=axioms:urr=on:i=882:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_1:1_sd=1:sos=on:ss=axioms:st=3.0:i=459:si=on:rawr=on:rtra=on_0");
    // Improves by expected 72.10696564517389 probs costing 79803 Mi
    // Sub-schedule for 15000Mi strat cap / 120000Mi overall limit
    quick.push("dis+1010_1:1024_fsr=off:newcnf=on:i=2078:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:7_av=off:awrs=converge:awrsf=40:br=off:bsd=on:cond=on:drc=off:nwc=3.0:plsq=on:plsqc=1:s2a=on:s2agt=16:to=lpo:urr=on:i=3576:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_acc=on:avsq=on:avsqc=2:avsqr=1,16:drc=off:nwc=5.0:sd=1:ss=included:st=4.0:urr=on:i=206:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_avsq=on:avsqc=2:avsql=on:avsqr=1,16:nwc=5.0:sac=on:spb=units:i=367:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_drc=off:flr=on:nwc=2.0:sac=on:urr=ec_only:i=2630:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:1_av=off:flr=on:ins=1:sos=on:sp=reverse_frequency:ss=axioms:urr=on:i=1806:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_acc=on:br=off:drc=off:nm=6:sac=on:sos=on:sp=frequency:to=lpo:urr=on:i=1065:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_av=off:bs=on:bsr=on:drc=off:etr=on:fde=none:fsd=on:fsdmm=1:fsr=off:gs=on:newcnf=on:nwc=10.0:s2a=on:sims=off:slsq=on:slsqc=0:slsqr=292,253:sp=frequency:ss=axioms:st=1.5:to=lpo:urr=ec_only:i=478:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bd=off:drc=off:lcm=reverse:nwc=5.0:sd=1:sgt=16:spb=goal_then_units:ss=axioms:to=lpo:i=74:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:227_abs=on:amm=off:avsq=on:avsqc=1:avsqr=97,32:awrs=converge:awrsf=256:bsr=unit_only:drc=off:fd=preordered:plsq=on:plsqc=1:plsql=on:plsqr=27942579,963352:sas=z3:slsq=on:slsqc=1:slsql=off:slsqr=307,512:sp=occurrence:ss=axioms:st=3.0:i=4310:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_bs=unit_only:flr=on:gs=on:nicw=on:nwc=2.0:s2a=on:sac=on:sas=z3:ss=axioms:st=2.6:updr=off:i=360:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_add=large:alpa=false:anc=none:fd=off:lcm=reverse:nwc=5.0:sd=2:sgt=20:ss=included:i=602:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:5_drc=off:s2a=on:s2at=1.5:i=653:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:16_slsq=on:slsqc=0:slsqr=1,1:sp=frequency:i=307:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_acc=on:br=off:nwc=10.0:s2a=on:s2agt=64:sac=on:urr=on:i=467:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_afr=on:alpa=true:amm=off:bd=off:bsr=on:flr=on:ins=2:slsq=on:slsqc=2:slsqr=31,16:sos=on:sp=reverse_frequency:to=lpo:i=1939:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_av=off:i=4822:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:128_awrs=converge:awrsf=30:bd=off:bs=unit_only:drc=off:fd=preordered:plsq=on:plsql=on:spb=goal:to=lpo:urr=ec_only:i=450:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_cond=fast:newcnf=on:plsq=on:sos=all:spb=goal:to=lpo:urr=on:i=2184:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:1_lcm=predicate:sos=on:sp=frequency:i=1652:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_aac=none:abs=on:add=large:afp=2000:afq=1.0:amm=off:avsq=on:avsqr=3,2:bs=unit_only:cond=on:drc=off:erd=off:fsr=off:gs=on:gsem=off:gsssp=full:newcnf=on:nicw=on:nwc=2.0:slsq=on:slsqc=2:slsqr=1,8:sp=frequency:spb=goal:ss=axioms:st=2.4:to=lpo:i=839:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_av=off:er=filter:slsq=on:slsqc=0:slsqr=1,1:sp=frequency:to=lpo:i=654:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:1_av=off:bd=off:bsr=unit_only:erd=off:etr=on:nm=0:sfv=off:sos=on:i=2226:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_flr=on:s2a=on:sp=occurrence:urr=on:i=478:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:64_anc=all:awrs=converge:drc=off:nicw=on:nwc=3.0:s2a=on:sac=on:spb=goal_then_units:i=336:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_aac=none:drc=off:fsr=off:nwc=2.0:sp=occurrence:ss=included:i=179:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+30_1:32_avsq=on:avsql=on:ep=RS:ins=1:nwc=10.0:s2a=on:sd=1:sgt=16:sp=frequency:ss=included:urr=on:uwa=one_side_interpreted:i=238:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:64_br=off:drc=off:flr=on:sp=reverse_arity:spb=goal_then_units:to=lpo:urr=ec_only:i=4588:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:14_awrs=converge:br=off:drc=off:ev=cautious:s2a=on:sfv=off:tgt=ground:tha=off:urr=on:i=1197:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=7218:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+3_1:1_atotf=0.2:fsr=off:kws=precedence:sp=weighted_frequency:spb=intro:tgt=ground:i=1916:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:12_abs=on:avsq=on:avsqr=5,31:bd=off:bsr=unit_only:plsq=on:plsql=on:plsqr=1,32:sac=on:sas=z3:spb=goal_then_units:tgt=full:to=lpo:i=14933:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_drc=off:fde=unused:gsp=on:ins=2:nwc=3.0:s2at=3.0:s2pl=no:sp=frequency:spb=goal_then_units:to=lpo:uwa=all:i=2781:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:4_avsq=on:avsqc=2:avsqr=1,16:newcnf=on:nwc=10.0:s2a=on:i=1033:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_3104939:689633_av=off:awrs=decay:awrsf=1:bce=on:cond=on:fde=unused:fsd=on:sp=const_min:thsq=on:thsqc=4:thsqd=64:thsqr=1,16:i=14024:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bd=preordered:drc=off:sp=frequency:to=lpo:urr=on:i=2649:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:4_av=off:bd=off:br=off:fsr=off:plsq=on:plsqr=20,11:s2a=on:urr=ec_only:i=3654:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_bce=on:gs=on:newcnf=on:plsq=on:plsqc=1:plsqr=32,1:skr=on:spb=goal_then_units:urr=ec_only:i=554:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_8:1_bd=off:br=off:fd=off:plsq=on:plsqr=278,15:s2at=1.5:slsq=on:slsqc=1:spb=goal_then_units:urr=ec_only:i=1843:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+31_160:31_acc=on:anc=all_dependent:awrs=decay:awrsf=32:sac=on:sd=1:sos=on:ss=axioms:st=2.0:to=lpo:i=177:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_aac=none:abs=on:bce=on:bd=off:bsr=unit_only:drc=off:fd=preordered:fsd=on:gve=cautious:lcm=reverse:nm=16:plsq=on:plsqc=1:plsqr=232,15:sfv=off:slsq=on:slsql=off:slsqr=3,2:sos=on:sp=weighted_frequency:i=375:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:1_av=off:drc=off:fd=preordered:foolp=on:ins=1:kws=inv_arity:plsq=on:plsqc=1:plsqr=3,25:s2at=2.0:slsq=on:slsqc=1:slsql=off:slsqr=1,8:sp=unary_frequency:urr=ec_only:uwa=one_side_interpreted:i=663:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:64_bd=off:lcm=predicate:sac=on:sp=const_frequency:urr=on:i=14627:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_av=off:gs=on:sos=all:urr=ec_only:i=3271:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:3_aac=none:bd=off:lcm=reverse:nwc=3.0:i=684:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_afp=100000:gsp=on:lwlo=on:nwc=3.0:sac=on:i=829:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:5_av=off:nwc=2.0:sos=all:updr=off:i=7247:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:4_av=off:bd=off:fde=unused:lcm=predicate:nwc=1.5:sp=const_frequency:i=253:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:rp=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=389:si=on:rawr=on:rtra=on_0");
    // Improves by expected 60.15631856377711 probs costing 119832 Mi
    // Sub-schedule for 50000Mi strat cap / 400000Mi overall limit
    quick.push("ott+1011_1:1_av=off:flr=on:ins=1:sos=on:sp=reverse_frequency:ss=axioms:urr=on:i=1806:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_br=off:plsq=on:plsqr=32,1:slsq=on:slsqc=1:slsqr=1,1:sp=frequency:to=lpo:urr=ec_only:i=1186:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_5:4_bs=unit_only:bsr=on:etr=on:fsd=on:fsr=off:irw=on:plsq=on:plsqc=1:plsqr=15,4:s2a=on:sac=on:updr=off:urr=ec_only:i=1200:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_atotf=0.1:lcm=predicate:nwc=5.0:rnwc=on:s2a=on:s2at=2.0:sac=on:sos=on:spb=goal_then_units:urr=on:i=1038:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:227_abs=on:amm=off:avsq=on:avsqc=1:avsqr=97,32:awrs=converge:awrsf=256:bsr=unit_only:drc=off:fd=preordered:plsq=on:plsqc=1:plsql=on:plsqr=27942579,963352:sas=z3:slsq=on:slsqc=1:slsql=off:slsqr=307,512:sp=occurrence:ss=axioms:st=3.0:i=4441:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_bs=unit_only:flr=on:gs=on:nicw=on:nwc=2.0:s2a=on:sac=on:sas=z3:ss=axioms:st=2.6:updr=off:i=2646:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:28_drc=off:fd=preordered:fsr=off:sp=frequency:to=lpo:i=6773:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:5_drc=off:s2a=on:s2at=1.5:i=653:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_nwc=2.0:spb=goal_then_units:ss=axioms:st=5.0:i=6891:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_s2a=on:s2at=1.2:sd=2:sgt=32:ss=axioms:i=625:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_afr=on:alpa=true:amm=off:bd=off:bsr=on:flr=on:ins=2:slsq=on:slsqc=2:slsqr=31,16:sos=on:sp=reverse_frequency:to=lpo:i=2997:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_fde=none:slsq=on:slsqc=0:slsqr=1,1:i=979:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_av=off:er=filter:slsq=on:slsqc=0:slsqr=1,1:sp=frequency:to=lpo:i=654:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_75:754_abs=on:add=large:anc=all:atotf=0.3115:drc=off:fd=preordered:fde=unused:gs=on:gsaa=from_current:gsem=off:nicw=on:nwc=4.0:slsq=on:slsqc=1:slsqr=1,1:spb=goal_then_units:to=lpo:i=6536:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_flr=on:s2a=on:sp=occurrence:urr=on:i=575:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1004_1:734_av=off:awrs=converge:awrsf=70:br=off:ep=RSTC:erd=off:gs=on:nwc=3.0:s2a=on:s2agt=16:sp=occurrence:updr=off:urr=on:i=10785:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+4_1:1_av=off:bd=off:lwlo=on:nwc=5.0:s2a=on:s2at=2.0:slsq=on:slsqc=2:slsql=off:slsqr=1,2:sp=frequency:i=4063:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+33_1:16_avsq=on:avsqr=23,8:plsq=on:plsqc=1:plsql=on:plsqr=4,1:sac=on:sas=z3:sp=frequency:to=lpo:urr=ec_only:i=1312:si=on:rawr=on:rtra=on_0");
    quick.push("dis+3_628:119_awrs=decay:awrsf=8:ep=RSTC:flr=on:plsq=on:plsqr=32,1:thsq=on:thsqc=64:thsqd=16:thsql=off:i=14753:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:4_abs=on:bsd=on:fsd=on:nwc=3.0:sas=z3:slsq=on:slsqc=2:slsql=off:slsqr=1,8:i=3899:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_av=off:nwc=2.0:spb=non_intro:tgt=full:to=lpo:urr=ec_only:i=3573:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_26459:191296_av=off:awrs=converge:awrsf=30:bd=preordered:bs=unit_only:drc=off:etr=on:flr=on:lwlo=on:nwc=5.0:plsq=on:plsqc=1:plsql=on:plsqr=1,32:skr=on:slsq=on:slsqr=18,107:sp=const_min:tgt=ground:to=lpo:urr=ec_only:i=6626:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:6_av=off:bce=on:ins=1:nwc=2.0:tgt=ground:thsq=on:thsqc=32:updr=off:i=8040:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:14_awrs=converge:br=off:drc=off:ev=cautious:s2a=on:sfv=off:tgt=ground:tha=off:urr=on:i=970:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+3_362687:487216_av=off:awrs=decay:awrsf=10:bd=preordered:br=off:drc=off:flr=on:foolp=on:fsr=off:ins=2:s2a=on:sp=occurrence:tgt=ground:urr=ec_only:i=5417:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=7155:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:16_bd=preordered:drc=off:s2a=on:tgt=ground:i=27947:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_av=off:bd=preordered:drc=off:fd=preordered:flr=on:foolp=on:fsr=off:lcm=reverse:nwc=2.0:s2a=on:s2at=3.0:sp=const_min:thsq=on:thsqc=64:thsqd=16:to=lpo:urr=on:i=2661:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:12_abs=on:avsq=on:avsqr=5,31:bd=off:bsr=unit_only:plsq=on:plsql=on:plsqr=1,32:sac=on:sas=z3:spb=goal_then_units:tgt=full:to=lpo:i=34070:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_1:1024_bd=off:bs=on:drc=off:kmz=on:kws=precedence:plsq=on:spb=goal:tgt=full:i=15150:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_fd=preordered:tgt=ground:i=5322:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:3_av=off:flr=on:sos=all:i=4460:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:35_av=off:bce=on:cond=on:foolp=on:lma=on:nwc=3.0:plsq=on:plsqc=2:plsqr=27,2:rnwc=on:s2a=on:s2at=3.0:s2pl=on:sos=all:sp=unary_first:thsq=on:thsqc=32:thsqd=32:thsql=off:urr=on:i=2204:si=on:rawr=on:rtra=on_0");
    quick.push("ott+0_1:1_av=off:bsr=unit_only:gsp=on:s2a=on:s2at=2.0:sos=on:i=2891:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:1_bd=preordered:ins=2:nicw=on:sas=z3:slsq=on:slsqc=1:slsql=off:slsqr=11,28:sp=frequency:urr=on:uwa=interpreted_only:i=6204:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_4:1_av=off:bsr=unit_only:cond=on:fd=preordered:flr=on:irw=on:lma=on:plsq=on:plsqc=2:plsql=on:sfv=off:sos=all:spb=units:to=lpo:i=1059:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+31_160:31_acc=on:anc=all_dependent:awrs=decay:awrsf=32:sac=on:sd=1:sos=on:ss=axioms:st=2.0:to=lpo:i=177:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_i=8689:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_5:1_av=off:awrs=decay:awrsf=20:bce=on:br=off:bsr=unit_only:cond=fast:drc=off:fd=preordered:ins=1:kws=inv_arity:nwc=5.0:plsq=on:plsqc=1:plsqr=29,237:s2a=on:slsq=on:slsqc=2:slsql=off:slsqr=1,4:sp=const_frequency:spb=goal:tgt=full:thi=overlap:urr=on:uwa=interpreted_only:i=8423:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_5:1_drc=off:kws=inv_arity_squared:nwc=5.0:plsq=on:plsqc=1:plsqr=32,1:s2a=on:s2at=2.1:urr=ec_only:i=18567:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:128_aac=none:acc=on:amm=off:atotf=0.1:bd=preordered:drc=off:fd=preordered:fde=none:gs=on:nicw=on:s2a=on:s2at=5.0:slsq=on:sp=const_max:spb=non_intro:tgt=ground:to=lpo:i=5620:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_sd=4:ss=axioms:st=3.0:i=5186:si=on:rawr=on:rtra=on_0");
    quick.push("dis+2_1:64_add=large:bce=on:bd=off:i=34585:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:sos=all:sp=occurrence:ss=included:i=16108:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+4_1:3_afp=4000:afr=on:anc=none:lma=on:nicw=on:nwc=1.2:sas=z3:i=18600:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:16_lma=on:nicw=on:sd=7:sp=const_frequency:ss=axioms:st=5.0:urr=ec_only:i=14422:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1003_1:1024_add=large:afr=on:cond=fast:fsr=off:gs=on:sos=on:sp=reverse_arity:i=11259:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_1:1_sd=1:sos=on:ss=axioms:st=3.0:i=506:si=on:rawr=on:rtra=on_0");
    // Improves by expected 85.78483446122088 probs costing 398782 Mi
    // Sub-schedule for 100000Mi strat cap / 800000Mi overall limit
    quick.push("dis+1011_5:4_bs=unit_only:bsr=on:etr=on:fsd=on:fsr=off:irw=on:plsq=on:plsqc=1:plsqr=15,4:s2a=on:sac=on:updr=off:urr=ec_only:i=1200:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:227_abs=on:amm=off:avsq=on:avsqc=1:avsqr=97,32:awrs=converge:awrsf=256:bsr=unit_only:drc=off:fd=preordered:plsq=on:plsqc=1:plsql=on:plsqr=27942579,963352:sas=z3:slsq=on:slsqc=1:slsql=off:slsqr=307,512:sp=occurrence:ss=axioms:st=3.0:i=4441:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:16_av=off:flr=on:nwc=5.0:s2a=on:sos=on:urr=on:i=2858:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_abs=on:amm=off:anc=all:br=off:bs=unit_only:sac=on:urr=on:i=13512:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:5_drc=off:s2a=on:s2at=1.5:i=653:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1_29:26_av=off:sp=frequency:to=lpo:i=13001:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_av=off:i=4822:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_cond=fast:newcnf=on:plsq=on:sos=all:spb=goal:to=lpo:urr=on:i=1908:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:1_lcm=predicate:sos=on:sp=frequency:i=1652:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_av=off:er=filter:slsq=on:slsqc=0:slsqr=1,1:sp=frequency:to=lpo:i=644:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_75:754_abs=on:add=large:anc=all:atotf=0.3115:drc=off:fd=preordered:fde=unused:gs=on:gsaa=from_current:gsem=off:nicw=on:nwc=4.0:slsq=on:slsqc=1:slsqr=1,1:spb=goal_then_units:to=lpo:i=16739:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:sd=2:sos=on:sp=reverse_arity:ss=axioms:to=lpo:i=18755:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_nwc=3.0:sgt=8:ss=included:i=4228:si=on:rawr=on:rtra=on_0");
    quick.push("ott+3_9107:782834_av=off:bce=on:br=off:bsdmm=1:bsr=unit_only:cond=on:dr=on:etr=on:flr=on:gs=on:lcm=predicate:lma=on:newcnf=on:nm=0:nwc=2.0:sims=off:spb=goal:updr=off:urr=on:i=22404:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_nwc=10.0:ss=included:st=1.5:urr=on:i=10509:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:8_aac=none:afp=1000:afq=2.0:atotf=0.5:bsd=on:drc=off:fde=none:newcnf=on:nwc=2.0:plsq=on:plsqr=1,32:sas=z3:sffsmt=on:slsq=on:slsqc=0:slsqr=1,1:urr=ec_only:i=42379:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:1_flr=on:s2a=on:sp=occurrence:urr=on:i=1788:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+3_8:1_anc=all:bd=off:nm=3:sac=on:urr=on:i=16942:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:1024_gsp=on:newcnf=on:nwc=2.0:s2a=on:s2at=3.0:sp=reverse_arity:spb=goal_then_units:updr=off:i=11247:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:40_av=off:bce=on:foolp=on:lma=on:nwc=3.4:plsq=on:plsqc=2:plsqr=32,1:rnwc=on:s2a=on:s2at=5.0:s2pl=on:sos=all:urr=on:i=4347:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:4_awrs=converge:drc=off:lwlo=on:sp=reverse_frequency:urr=ec_only:i=12332:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:1_abs=on:bd=off:flr=on:nm=0:s2at=3.0:sas=z3:sfv=off:slsq=on:slsqc=2:slsqr=46,31:sp=const_frequency:tgt=ground:tha=some:thi=overlap:thitd=on:thsq=on:thsqc=32:thsqd=32:thsqr=7,4:i=35619:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:4_abs=on:bsd=on:fsd=on:nwc=3.0:sas=z3:slsq=on:slsqc=2:slsql=off:slsqr=1,8:i=7159:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_plsq=on:plsqc=1:plsqr=32,1:tha=some:thi=all:uwa=one_side_constant:i=6381:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:6_av=off:bce=on:ins=1:nwc=2.0:tgt=ground:thsq=on:thsqc=32:updr=off:i=3311:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:14_awrs=converge:br=off:drc=off:ev=cautious:s2a=on:sfv=off:tgt=ground:tha=off:urr=on:i=1268:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:32_abs=on:bd=off:br=off:flr=on:kws=frequency:nicw=on:plsq=on:plsqr=1,16:s2a=on:s2at=2.0:sac=on:sas=z3:urr=ec_only:i=18451:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_av=off:nm=0:nwc=1.5:tgt=full:tha=off:i=15723:si=on:rawr=on:rtra=on_0");
    quick.push("dis+4_18398:962327_av=off:awrs=decay:awrsf=16:erd=off:sp=const_frequency:spb=goal:to=lpo:i=7747:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ev=cautious:gve=force:nwc=5.0:i=14351:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=33434:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_drc=off:tgt=full:i=15938:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:128_drc=off:ins=1:sp=const_frequency:tgt=ground:i=37539:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_3104939:689633_av=off:awrs=decay:awrsf=1:bce=on:cond=on:fde=unused:fsd=on:sp=const_min:thsq=on:thsqc=4:thsqd=64:thsqr=1,16:i=15013:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+33_1:4_lwlo=on:s2a=on:tgt=ground:i=27751:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:128_awrs=converge:awrsf=128:bsd=on:fd=preordered:fsr=off:gs=on:nwc=3.0:sp=const_frequency:tgt=full:urr=on:uwa=one_side_constant:i=4323:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1_2:3_atotf=0.2:avsq=on:avsqr=1,16:br=off:bsr=unit_only:canc=cautious:fd=preordered:foolp=on:gs=on:ins=1:lma=on:nwc=2.0:sas=z3:sp=unary_frequency:tha=some:thi=neg_eq:to=lpo:uace=off:updr=off:urr=ec_only:uwa=one_side_constant:i=5903:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bsr=unit_only:cond=on:flr=on:newcnf=on:nwc=10.0:sas=z3:to=lpo:i=3826:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:3_afr=on:alpa=random:amm=sco:awrs=converge:awrsf=220:bce=on:bd=preordered:fd=preordered:flr=on:fsd=on:gs=on:gsaa=from_current:ins=1:nwc=5.0:plsq=on:plsqc=1:plsql=on:plsqr=1,32:s2a=on:s2at=2.0:sas=z3:slsq=on:slsqc=2:slsql=off:slsqr=5,23:sp=reverse_arity:spb=goal_then_units:to=lpo:uwa=one_side_constant:i=21329:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:35_av=off:bce=on:cond=on:foolp=on:lma=on:nwc=3.0:plsq=on:plsqc=2:plsqr=27,2:rnwc=on:s2a=on:s2at=3.0:s2pl=on:sos=all:sp=unary_first:thsq=on:thsqc=32:thsqd=32:thsql=off:urr=on:i=2204:si=on:rawr=on:rtra=on_0");
    quick.push("dis+20_1:20_av=off:awrs=converge:bs=on:fsr=off:nwc=3.0:urr=ec_only:i=1573:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:128_abs=on:atotf=0.2:gsp=on:nwc=10.0:urr=on:i=10999:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_5:1_av=off:awrs=decay:awrsf=20:bce=on:br=off:bsr=unit_only:cond=fast:drc=off:fd=preordered:ins=1:kws=inv_arity:nwc=5.0:plsq=on:plsqc=1:plsqr=29,237:s2a=on:slsq=on:slsqc=2:slsql=off:slsqr=1,4:sp=const_frequency:spb=goal:tgt=full:thi=overlap:urr=on:uwa=interpreted_only:i=8423:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:3_abs=on:amm=sco:avsq=on:bsd=on:fd=preordered:gve=cautious:kws=inv_arity_squared:sas=z3:sos=on:sp=const_max:spb=goal_then_units:tgt=full:uwa=interpreted_only:i=5945:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_5:1_av=off:sd=1:sos=all:ss=axioms:st=5.0:i=7955:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:10_av=off:gs=on:lma=on:sos=all:i=15588:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:2_lcm=predicate:sp=reverse_arity:urr=ec_only:i=10198:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:3_av=off:lma=on:nwc=1.5:sos=all:updr=off:i=64021:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:3_av=off:bs=unit_only:cond=on:lwlo=on:sp=weighted_frequency:i=87988:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:16_add=large:amm=sco:bs=unit_only:fsr=off:nicw=on:sas=z3:sos=all:i=19507:si=on:rawr=on:rtra=on_0");
    quick.push("lrs-2_1:1_afp=1000:anc=none:bce=on:bd=off:gs=on:lwlo=on:sac=on:stl=30:i=15608:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_br=off:plsq=on:plsqr=32,1:rp=on:s2a=on:urr=ec_only:i=2950:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1004_1:1_anc=all_dependent:bsr=on:gs=on:nwc=3.0:rp=on:s2a=on:s2at=2.0:sac=on:slsq=on:slsqc=0:slsql=off:slsqr=1,4:sp=reverse_arity:spb=goal_then_units:to=lpo:urr=on:i=6696:si=on:rawr=on:rtra=on_0");
    // Improves by expected 50.69949270791716 probs costing 799912 Mi
    // Sub-schedule for 150000Mi strat cap / 1200000Mi overall limit
    quick.push("dis+1011_5:4_bs=unit_only:bsr=on:etr=on:fsd=on:fsr=off:irw=on:plsq=on:plsqc=1:plsqr=15,4:s2a=on:sac=on:updr=off:urr=ec_only:i=1200:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:227_abs=on:amm=off:avsq=on:avsqc=1:avsqr=97,32:awrs=converge:awrsf=256:bsr=unit_only:drc=off:fd=preordered:plsq=on:plsqc=1:plsql=on:plsqr=27942579,963352:sas=z3:slsq=on:slsqc=1:slsql=off:slsqr=307,512:sp=occurrence:ss=axioms:st=3.0:i=4425:si=on:rawr=on:rtra=on_0");
    quick.push("dis+21_1:1_av=off:er=filter:slsq=on:slsqc=0:slsqr=1,1:sp=frequency:to=lpo:i=2028:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_75:754_abs=on:add=large:anc=all:atotf=0.3115:drc=off:fd=preordered:fde=unused:gs=on:gsaa=from_current:gsem=off:nicw=on:nwc=4.0:slsq=on:slsqc=1:slsqr=1,1:spb=goal_then_units:to=lpo:i=5167:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_anc=all_dependent:avsq=on:avsqc=2:avsqr=131,15:flr=on:fsd=on:ins=2:newcnf=on:sac=on:skr=on:sos=on:sp=occurrence:updr=off:urr=ec_only:i=4187:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1004_1:734_av=off:awrs=converge:awrsf=70:br=off:ep=RSTC:erd=off:gs=on:nwc=3.0:s2a=on:s2agt=16:sp=occurrence:updr=off:urr=on:i=10722:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+35_1:128_i=102621:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:28_bsr=unit_only:flr=on:sos=on:i=24448:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_aac=none:bsr=on:ep=R:fsr=off:lma=on:sos=all:i=23883:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:69_aac=none:add=large:anc=all_dependent:atotf=0.0280618:bce=on:bsr=on:flr=on:gs=on:ins=3:lcm=predicate:newcnf=on:s2a=on:sac=on:sas=z3:sp=const_min:tgt=full:thsq=on:thsqc=32:thsqd=16:i=25212:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:4_abs=on:bsd=on:fsd=on:nwc=3.0:sas=z3:slsq=on:slsqc=2:slsql=off:slsqr=1,8:i=4153:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_aac=none:acc=model:atotf=0.2:awrs=converge:bd=preordered:bs=on:sp=occurrence:tgt=full:i=39244:si=on:rawr=on:rtra=on_0");
    quick.push("dis+20_1:12_aac=none:acc=model:awrs=converge:fd=preordered:fsr=off:nicw=on:nwc=3.0:s2a=on:s2agt=16:spb=goal:to=lpo:i=25706:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=93064:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:16_bd=preordered:drc=off:s2a=on:tgt=ground:i=20732:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_bd=preordered:drc=off:fde=unused:slsq=on:slsqr=10,31:sp=const_min:tgt=ground:to=lpo:urr=ec_only:i=28123:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_34:25_av=off:awrs=decay:awrsf=23:bce=on:cond=on:flr=on:irw=on:kws=precedence:s2a=on:s2agt=30:s2at=3.2:slsq=on:slsqr=1,4:sp=const_min:spb=intro:updr=off:urr=ec_only:i=46659:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:512_drc=off:fd=preordered:ins=2:kws=precedence:s2a=on:sp=unary_first:spb=intro:tgt=ground:i=37380:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_3104939:689633_av=off:awrs=decay:awrsf=1:bce=on:cond=on:fde=unused:fsd=on:sp=const_min:thsq=on:thsqc=4:thsqd=64:thsqr=1,16:i=13503:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:128_awrs=converge:awrsf=128:bsd=on:fd=preordered:fsr=off:gs=on:nwc=3.0:sp=const_frequency:tgt=full:urr=on:uwa=one_side_constant:i=4323:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_1:1024_bd=off:bs=on:drc=off:kmz=on:kws=precedence:plsq=on:spb=goal:tgt=full:i=67469:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1_2:3_atotf=0.2:avsq=on:avsqr=1,16:br=off:bsr=unit_only:canc=cautious:fd=preordered:foolp=on:gs=on:ins=1:lma=on:nwc=2.0:sas=z3:sp=unary_frequency:tha=some:thi=neg_eq:to=lpo:uace=off:updr=off:urr=ec_only:uwa=one_side_constant:i=5903:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:3_afr=on:alpa=random:amm=sco:awrs=converge:awrsf=220:bce=on:bd=preordered:fd=preordered:flr=on:fsd=on:gs=on:gsaa=from_current:ins=1:nwc=5.0:plsq=on:plsqc=1:plsql=on:plsqr=1,32:s2a=on:s2at=2.0:sas=z3:slsq=on:slsqc=2:slsql=off:slsqr=5,23:sp=reverse_arity:spb=goal_then_units:to=lpo:uwa=one_side_constant:i=21329:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:1_bd=preordered:ins=2:nicw=on:sas=z3:slsq=on:slsqc=1:slsql=off:slsqr=11,28:sp=frequency:urr=on:uwa=interpreted_only:i=6204:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:128_abs=on:atotf=0.2:gsp=on:nwc=10.0:urr=on:i=10999:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1224:547607_av=off:awrs=decay:awrsf=18:bd=off:bsd=on:ins=1:slsq=on:slsqc=2:slsql=off:slsqr=1,8:spb=goal:tgt=full:to=lpo:i=73949:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:128_aac=none:acc=on:amm=off:atotf=0.1:bd=preordered:drc=off:fd=preordered:fde=none:gs=on:nicw=on:s2a=on:s2at=5.0:slsq=on:sp=const_max:spb=non_intro:tgt=ground:to=lpo:i=78808:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:3_abs=on:amm=sco:avsq=on:bsd=on:fd=preordered:gve=cautious:kws=inv_arity_squared:sas=z3:sos=on:sp=const_max:spb=goal_then_units:tgt=full:uwa=interpreted_only:i=5945:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:3_av=off:sos=all:sp=const_frequency:i=19165:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_anc=all_dependent:bs=on:bsr=on:i=44149:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_afq=1.0:bd=off:bsr=unit_only:irw=on:i=99281:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1003_1:10_amm=off:bce=on:br=off:bsr=unit_only:lma=on:nicw=on:sac=on:uhcvi=on:urr=on:i=101117:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:6_awrs=decay:bsr=unit_only:fde=none:gs=on:nwc=1.5:s2a=on:sas=z3:sp=unary_first:ss=axioms:updr=off:i=6239:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_acc=on:urr=ec_only:i=31248:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=5:sp=occurrence:ss=axioms:st=3.0:i=12598:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:sos=all:sp=occurrence:ss=included:i=29728:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:16_lma=on:nicw=on:sd=7:sp=const_frequency:ss=axioms:st=5.0:urr=ec_only:i=42776:si=on:rawr=on:rtra=on_0");
    quick.push("lrs-2_1:1_afp=1000:anc=none:bce=on:bd=off:gs=on:lwlo=on:sac=on:stl=30:i=16103:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1004_1:1_anc=all_dependent:bsr=on:gs=on:nwc=3.0:rp=on:s2a=on:s2at=2.0:sac=on:slsq=on:slsqc=0:slsql=off:slsqr=1,4:sp=reverse_arity:spb=goal_then_units:to=lpo:urr=on:i=6696:si=on:rawr=on:rtra=on_0");
    // Improves by expected 30.1748931064352 probs costing 1196447 Mi
    // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
    quick.push("dis+1011_1:227_abs=on:amm=off:avsq=on:avsqc=1:avsqr=97,32:awrs=converge:awrsf=256:bsr=unit_only:drc=off:fd=preordered:plsq=on:plsqc=1:plsql=on:plsqr=27942579,963352:sas=z3:slsq=on:slsqc=1:slsql=off:slsqr=307,512:sp=occurrence:ss=axioms:st=3.0:i=4425:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_75:754_abs=on:add=large:anc=all:atotf=0.3115:drc=off:fd=preordered:fde=unused:gs=on:gsaa=from_current:gsem=off:nicw=on:nwc=4.0:slsq=on:slsqc=1:slsqr=1,1:spb=goal_then_units:to=lpo:i=16739:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sos=all:ss=axioms:st=1.5:i=12816:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_nwc=10.0:ss=included:st=1.5:urr=on:i=12840:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+3_8:1_anc=all:bd=off:nm=3:sac=on:urr=on:i=16942:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_br=off:gsp=on:nm=4:skr=on:urr=on:i=163802:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:1_ep=RS:fs=off:fsr=off:s2a=on:s2at=1.5:sac=on:sos=all:updr=off:i=25640:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1024_afp=20:afq=2.0:anc=all:bd=preordered:bs=unit_only:drc=off:sac=on:sos=on:to=lpo:i=81536:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_397:95149_awrs=decay:awrsf=30:s2a=on:urr=on:i=73193:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+35_1:1024_bsr=on:flr=on:to=lpo:i=79350:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_s2a=on:s2at=1.5:i=28275:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1024_afp=1000:avsq=on:awrs=converge:bd=preordered:drc=off:ins=1:ss=axioms:st=5.0:to=lpo:uwa=interpreted_only:i=134372:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:28_bsr=unit_only:flr=on:sos=on:i=24448:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1544279:568915_av=off:awrs=decay:drc=off:fd=preordered:foolp=on:fsr=off:plsq=on:sims=off:sos=on:urr=on:i=17001:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:4_awrs=converge:drc=off:lwlo=on:sp=reverse_frequency:urr=ec_only:i=8616:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_aac=none:bsr=on:ep=R:fsr=off:lma=on:sos=all:i=23883:si=on:rawr=on:rtra=on_0");
    quick.push("dis+3_628:119_awrs=decay:awrsf=8:ep=RSTC:flr=on:plsq=on:plsqr=32,1:thsq=on:thsqc=64:thsqd=16:thsql=off:i=12917:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:69_aac=none:add=large:anc=all_dependent:atotf=0.0280618:bce=on:bsr=on:flr=on:gs=on:ins=3:lcm=predicate:newcnf=on:s2a=on:sac=on:sas=z3:sp=const_min:tgt=full:thsq=on:thsqc=32:thsqd=16:i=25212:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:4_abs=on:bsd=on:fsd=on:nwc=3.0:sas=z3:slsq=on:slsqc=2:slsql=off:slsqr=1,8:i=17691:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_aac=none:acc=model:atotf=0.2:awrs=converge:bd=preordered:bs=on:sp=occurrence:tgt=full:i=42806:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_awrs=converge:drc=off:kws=inv_frequency:tgt=full:i=18948:si=on:rawr=on:rtra=on_0");
    quick.push("dis+20_1:12_aac=none:acc=model:awrs=converge:fd=preordered:fsr=off:nicw=on:nwc=3.0:s2a=on:s2agt=16:spb=goal:to=lpo:i=25706:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_ev=cautious:gve=force:nwc=5.0:i=21929:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=117397:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:16_bd=preordered:drc=off:s2a=on:tgt=ground:i=20732:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1_bd=preordered:drc=off:fde=unused:slsq=on:slsqr=10,31:sp=const_min:tgt=ground:to=lpo:urr=ec_only:i=28123:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_3104939:689633_av=off:awrs=decay:awrsf=1:bs=on:er=filter:fd=preordered:fde=none:foolp=on:fsd=on:kws=frequency:nwc=1.5:sp=const_max:spb=non_intro:tgt=ground:thi=all:thsq=on:thsqc=1:thsqd=32:thsqr=1,32:i=57189:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_kws=precedence:lwlo=on:tgt=ground:i=450001:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_drc=off:tgt=full:i=15938:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:br=off:sas=z3:spb=goal:tgt=full:tha=some:to=lpo:uwa=all:i=85807:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:128_awrs=converge:awrsf=128:bsd=on:fd=preordered:fsr=off:gs=on:nwc=3.0:sp=const_frequency:tgt=full:urr=on:uwa=one_side_constant:i=32064:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_1:1024_bd=off:bs=on:drc=off:kmz=on:kws=precedence:plsq=on:spb=goal:tgt=full:i=65919:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1_2:3_atotf=0.2:avsq=on:avsqr=1,16:br=off:bsr=unit_only:canc=cautious:fd=preordered:foolp=on:gs=on:ins=1:lma=on:nwc=2.0:sas=z3:sp=unary_frequency:tha=some:thi=neg_eq:to=lpo:uace=off:updr=off:urr=ec_only:uwa=one_side_constant:i=5903:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:3_afr=on:alpa=random:amm=sco:awrs=converge:awrsf=220:bce=on:bd=preordered:fd=preordered:flr=on:fsd=on:gs=on:gsaa=from_current:ins=1:nwc=5.0:plsq=on:plsqc=1:plsql=on:plsqr=1,32:s2a=on:s2at=2.0:sas=z3:slsq=on:slsqc=2:slsql=off:slsqr=5,23:sp=reverse_arity:spb=goal_then_units:to=lpo:uwa=one_side_constant:i=21329:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_i=77427:si=on:rawr=on:rtra=on_0");
    quick.push("dis+11_1:128_abs=on:atotf=0.2:gsp=on:nwc=10.0:urr=on:i=10999:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:128_aac=none:acc=on:amm=off:atotf=0.1:bd=preordered:drc=off:fd=preordered:fde=none:gs=on:nicw=on:s2a=on:s2at=5.0:slsq=on:sp=const_max:spb=non_intro:tgt=ground:to=lpo:i=78808:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:5_bs=unit_only:drc=off:ins=1:nwc=2.16:rnwc=on:slsq=on:slsqr=13,149:sp=const_min:tgt=ground:to=lpo:uwa=interpreted_only:i=78747:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:sp=occurrence:i=119235:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:2_av=off:cond=fast:nwc=10.0:i=11060:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:3_av=off:sos=all:sp=const_frequency:i=19165:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_anc=all_dependent:bs=on:bsr=unit_only:i=24248:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_2:3_av=off:cond=on:lwlo=on:nwc=2.0:i=260433:si=on:rawr=on:rtra=on_0");
    quick.push("dis-11_1:32_av=off:gs=on:lma=on:updr=off:i=17102:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:4_av=off:sos=all:i=69001:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:2_av=off:gs=on:nwc=10.0:i=10610:si=on:rawr=on:rtra=on_0");
    quick.push("dis+2_1:64_add=large:bce=on:bd=off:i=209249:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1003_1:10_amm=off:bce=on:br=off:bsr=unit_only:lma=on:nicw=on:sac=on:uhcvi=on:urr=on:i=296770:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:1_acc=on:urr=ec_only:i=31248:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_nwc=5.0:sd=4:ss=included:st=5.0:i=96687:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=5:sp=occurrence:ss=axioms:st=3.0:i=12598:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:3_av=off:bs=unit_only:cond=on:lwlo=on:sp=weighted_frequency:i=113725:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1004_1:1_anc=all_dependent:bsr=on:gs=on:nwc=3.0:rp=on:s2a=on:s2at=2.0:sac=on:slsq=on:slsqc=0:slsql=off:slsqr=1,4:sp=reverse_arity:spb=goal_then_units:to=lpo:urr=on:i=6696:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:rp=on:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=286610:si=on:rawr=on:rtra=on_0");
    // Improves by expected 37.53181284763515 probs costing 3962574 Mi
    // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
    quick.push("dis+1011_1:227_abs=on:amm=off:avsq=on:avsqc=1:avsqr=97,32:awrs=converge:awrsf=256:bsr=unit_only:drc=off:fd=preordered:plsq=on:plsqc=1:plsql=on:plsqr=27942579,963352:sas=z3:slsq=on:slsqc=1:slsql=off:slsqr=307,512:sp=occurrence:ss=axioms:st=3.0:i=4425:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_75:754_abs=on:add=large:anc=all:atotf=0.3115:drc=off:fd=preordered:fde=unused:gs=on:gsaa=from_current:gsem=off:nicw=on:nwc=4.0:slsq=on:slsqc=1:slsqr=1,1:spb=goal_then_units:to=lpo:i=16739:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sos=on:ss=included:st=1.2:urr=on:i=491465:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=R:gsp=on:nm=0:sos=on:spb=units:ss=included:i=120001:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+21_1:1_ep=RS:fs=off:fsr=off:s2a=on:s2at=1.5:sac=on:sos=all:updr=off:i=25640:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_397:95149_awrs=decay:awrsf=30:s2a=on:urr=on:i=73193:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=192739:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+35_1:1024_bsr=on:flr=on:to=lpo:i=79350:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:1_s2a=on:s2at=1.5:i=28275:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:1024_afp=1000:avsq=on:awrs=converge:bd=preordered:drc=off:ins=1:ss=axioms:st=5.0:to=lpo:uwa=interpreted_only:i=134372:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:28_bsr=unit_only:flr=on:sos=on:i=24448:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_aac=none:bsr=on:ep=R:fsr=off:lma=on:sos=all:i=23883:si=on:rawr=on:rtra=on_0");
    quick.push("dis+10_1:4_abs=on:bsd=on:fsd=on:nwc=3.0:sas=z3:slsq=on:slsqc=2:slsql=off:slsqr=1,8:i=7159:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:32_aac=none:acc=model:atotf=0.2:awrs=converge:bd=preordered:bs=on:sp=occurrence:tgt=full:i=42806:si=on:rawr=on:rtra=on_0");
    quick.push("dis+20_1:12_aac=none:acc=model:awrs=converge:fd=preordered:fsr=off:nicw=on:nwc=3.0:s2a=on:s2agt=16:spb=goal:to=lpo:i=25706:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:12_drc=off:fd=preordered:tgt=full:i=234351:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=148043:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:16_bd=preordered:drc=off:s2a=on:tgt=ground:i=20732:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_kws=precedence:lwlo=on:tgt=ground:i=411698:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1_2:3_atotf=0.2:avsq=on:avsqr=1,16:br=off:bsr=unit_only:canc=cautious:fd=preordered:foolp=on:gs=on:ins=1:lma=on:nwc=2.0:sas=z3:sp=unary_frequency:tha=some:thi=neg_eq:to=lpo:uace=off:updr=off:urr=ec_only:uwa=one_side_constant:i=5903:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:3_afr=on:alpa=random:amm=sco:awrs=converge:awrsf=220:bce=on:bd=preordered:fd=preordered:flr=on:fsd=on:gs=on:gsaa=from_current:ins=1:nwc=5.0:plsq=on:plsqc=1:plsql=on:plsqr=1,32:s2a=on:s2at=2.0:sas=z3:slsq=on:slsqc=2:slsql=off:slsqr=5,23:sp=reverse_arity:spb=goal_then_units:to=lpo:uwa=one_side_constant:i=21329:si=on:rawr=on:rtra=on_0");
    quick.push("fmb+10_1:1_i=77427:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1224:547607_av=off:awrs=decay:awrsf=18:bd=off:bsd=on:ins=1:slsq=on:slsqc=2:slsql=off:slsqr=1,8:spb=goal:tgt=full:to=lpo:i=73949:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:128_aac=none:acc=on:amm=off:atotf=0.1:bd=preordered:drc=off:fd=preordered:fde=none:gs=on:nicw=on:s2a=on:s2at=5.0:slsq=on:sp=const_max:spb=non_intro:tgt=ground:to=lpo:i=78808:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:2_av=off:cond=fast:nwc=10.0:i=11060:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:3_av=off:sos=all:sp=const_frequency:i=286633:si=on:rawr=on:rtra=on_0");
    quick.push("dis-11_1:32_av=off:gs=on:lma=on:updr=off:i=17102:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:4_av=off:sos=all:i=69001:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_afp=100000:gsp=on:lwlo=on:nwc=3.0:sac=on:i=471456:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:2_av=off:gs=on:nwc=10.0:i=10610:si=on:rawr=on:rtra=on_0");
    quick.push("dis+2_1:64_add=large:bce=on:bd=off:i=67591:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1011_1:16_lma=on:nicw=on:sd=7:sp=const_frequency:ss=axioms:st=5.0:urr=ec_only:i=42776:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:3_av=off:bs=unit_only:cond=on:lwlo=on:sp=weighted_frequency:i=86925:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_bd=off:lwlo=on:i=140846:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1004_1:1_anc=all_dependent:bsr=on:gs=on:nwc=3.0:rp=on:s2a=on:s2at=2.0:sac=on:slsq=on:slsqc=0:slsql=off:slsqr=1,4:sp=reverse_arity:spb=goal_then_units:to=lpo:urr=on:i=6696:si=on:rawr=on:rtra=on_0");
    // Improves by expected 9.79862444760018 probs costing 3915823 Mi
    // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
    quick.push("ott+10_75:754_abs=on:add=large:anc=all:atotf=0.3115:drc=off:fd=preordered:fde=unused:gs=on:gsaa=from_current:gsem=off:nicw=on:nwc=4.0:slsq=on:slsqc=1:slsqr=1,1:spb=goal_then_units:to=lpo:i=62126:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_sos=on:ss=included:st=1.2:urr=on:i=490001:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_ep=R:gsp=on:nm=0:sos=on:spb=units:ss=included:i=120001:si=on:rawr=on:rtra=on_0");
    quick.push("ott+11_397:95149_awrs=decay:awrsf=30:s2a=on:urr=on:i=73193:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=192739:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+35_1:1024_bsr=on:flr=on:to=lpo:i=79350:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1002_1:28_bsr=unit_only:flr=on:sos=on:i=24448:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_aac=none:bsr=on:ep=R:fsr=off:lma=on:sos=all:i=23883:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1002_1:12_drc=off:fd=preordered:tgt=full:i=234351:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1011_1:64_av=off:bce=on:bd=off:bsd=on:cond=on:flr=on:foolp=on:nwc=2.0:plsq=on:plsqc=1:plsqr=37,6:s2agt=32:slsq=on:slsqc=1:slsql=off:slsqr=17,16:tgt=full:i=337199:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+10_1:1_kws=precedence:lwlo=on:tgt=ground:i=285611:si=on:rawr=on:rtra=on_0");
    quick.push("ott+10_1:128_aac=none:acc=on:amm=off:atotf=0.1:bd=preordered:drc=off:fd=preordered:fde=none:gs=on:nicw=on:s2a=on:s2at=5.0:slsq=on:sp=const_max:spb=non_intro:tgt=ground:to=lpo:i=78808:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_1:2_av=off:cond=fast:nwc=10.0:i=11060:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+11_2:3_av=off:cond=on:lwlo=on:nwc=2.0:i=245041:si=on:rawr=on:rtra=on_0");
    quick.push("dis-11_1:32_av=off:gs=on:lma=on:updr=off:i=17102:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:1_afp=100000:gsp=on:lwlo=on:nwc=3.0:sac=on:i=471456:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+1011_1:3_av=off:bs=unit_only:cond=on:lwlo=on:sp=weighted_frequency:i=86925:si=on:rawr=on:rtra=on_0");
    quick.push("ott+1004_1:1_anc=all_dependent:bsr=on:gs=on:nwc=3.0:rp=on:s2a=on:s2at=2.0:sac=on:slsq=on:slsqc=0:slsql=off:slsqr=1,4:sp=reverse_arity:spb=goal_then_units:to=lpo:urr=on:i=6696:si=on:rawr=on:rtra=on_0");
    quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:rp=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=180993:si=on:rawr=on:rtra=on_0");
    quick.push("lrs+2_1:128_awrs=decay:awrsf=20:drc=off:fsd=on:lwlo=on:nm=2:nwc=1.94:rp=on:spb=units:thsq=on:thsqc=32:thsqd=32:thsqr=4,7:i=263998:si=on:rawr=on:rtra=on_0");
    // Improves by expected 4.397794165391981 probs costing 3627682 Mi
    // Overall score 4562.511209545269 probs on average / budget 14267187 Mi
  }
}

void Schedules::getSnakeTptpSatSchedule(const Shell::Property& property, Schedule& quick) {
  // problemsFNT.txt
  // Champion singleton-schedule for 200000Mi
   quick.push("fmb+10_1:1_bce=on:fmbsr=1.5:nm=4:skr=on:i=191324:si=on:rawr=on:rtra=on_0");
  // Improves by expected 1856.5193556018971 probs costing 191323 Mi
  // Sub-schedule for 50Mi strat cap / 400Mi overall limit
   quick.push("ott+10_1:32_abs=on:br=off:urr=ec_only:i=50:si=on:rawr=on:rtra=on_0");
   quick.push("ott+4_1:1_av=off:bd=off:nwc=5.0:s2a=on:s2at=2.0:slsq=on:slsqc=2:slsql=off:slsqr=1,2:sp=frequency:i=37:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:32_bd=off:fsr=off:newcnf=on:tgt=full:i=51:si=on:rawr=on:rtra=on_0");
   quick.push("ott+33_1:4_s2a=on:tgt=ground:i=51:si=on:rawr=on:rtra=on_0");
   quick.push("dis+34_1:32_abs=on:add=off:bsr=on:gsp=on:sp=weighted_frequency:i=48:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_fmbsr=2.0:nm=4:skr=on:i=51:si=on:rawr=on:rtra=on_0");
   quick.push("dis+10_1:1_fsd=on:sp=occurrence:i=7:si=on:rawr=on:rtra=on_0");
   quick.push("dis+2_1:64_add=large:bce=on:bd=off:i=2:si=on:rawr=on:rtra=on_0");
   quick.push("ott-1_1:6_av=off:cond=on:fsr=off:nwc=3.0:i=51:si=on:rawr=on:rtra=on_0");
   quick.push("ott+2_1:1_fsr=off:gsp=on:i=50:si=on:rawr=on:rtra=on_0");
  // Improves by expected 95.35596882712122 probs costing 388 Mi
  // Sub-schedule for 100Mi strat cap / 800Mi overall limit
   quick.push("ott+10_1:32_bd=off:fsr=off:newcnf=on:tgt=full:i=100:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:28_bd=off:bs=on:tgt=ground:i=101:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:5_bd=off:tgt=full:i=99:si=on:rawr=on:rtra=on_0");
   quick.push("ott+11_2:3_av=off:fde=unused:nwc=5.0:tgt=ground:i=75:si=on:rawr=on:rtra=on_0");
   quick.push("dis+34_1:32_abs=on:add=off:bsr=on:gsp=on:sp=weighted_frequency:i=99:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_bce=on:i=59:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:1_tgt=ground:i=100:si=on:rawr=on:rtra=on_0");
   quick.push("ott+4_1:1_av=off:bd=off:nwc=5.0:rp=on:s2a=on:s2at=2.0:slsq=on:slsqc=2:slsql=off:slsqr=1,2:sp=frequency:i=100:si=on:rawr=on:rtra=on_0");
  // Improves by expected 12.8888583651196 probs costing 792 Mi
  // Sub-schedule for 500Mi strat cap / 4000Mi overall limit
   quick.push("ott+10_1:8_bsd=on:fsd=on:lcm=predicate:nwc=5.0:s2a=on:s2at=1.5:spb=goal_then_units:i=176:si=on:rawr=on:rtra=on_0");
   quick.push("ott+3_1:1_gsp=on:lcm=predicate:i=138:si=on:rawr=on:rtra=on_0");
   quick.push("dis+21_1:1_av=off:er=filter:slsq=on:slsqc=0:slsqr=1,1:sp=frequency:to=lpo:i=498:si=on:rawr=on:rtra=on_0");
   quick.push("ott+11_1:1_drc=off:nwc=5.0:slsq=on:slsqc=1:spb=goal_then_units:to=lpo:i=467:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:1_kws=precedence:tgt=ground:i=482:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:5_bd=off:tgt=full:i=500:si=on:rawr=on:rtra=on_0");
   quick.push("ott+11_2:3_av=off:fde=unused:nwc=5.0:tgt=ground:i=177:si=on:rawr=on:rtra=on_0");
   quick.push("ott+33_1:4_s2a=on:tgt=ground:i=439:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_7:2_awrs=decay:awrsf=8:bd=preordered:drc=off:fd=preordered:fde=unused:fsr=off:slsq=on:slsqc=2:slsqr=5,8:sp=const_min:spb=units:to=lpo:i=355:si=on:rawr=on:rtra=on_0");
   quick.push("dis+34_1:32_abs=on:add=off:bsr=on:gsp=on:sp=weighted_frequency:i=388:si=on:rawr=on:rtra=on_0");
   quick.push("ott-1_1:6_av=off:cond=on:fsr=off:nwc=3.0:i=211:si=on:rawr=on:rtra=on_0");
   quick.push("dis+22_1:128_bsd=on:rp=on:slsq=on:slsqc=1:slsqr=1,6:sp=frequency:spb=goal:thsq=on:thsqc=16:thsqd=1:thsql=off:i=90:si=on:rawr=on:rtra=on_0");
  // Improves by expected 27.24796872611255 probs costing 3976 Mi
  // Sub-schedule for 1000Mi strat cap / 8000Mi overall limit
   quick.push("ott+1_1:2_i=920:si=on:rawr=on:rtra=on_0");
   quick.push("ott+1_1:7_bd=off:i=934:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:50_bsr=unit_only:drc=off:fd=preordered:sp=frequency:i=747:si=on:rawr=on:rtra=on_0");
   quick.push("dis+21_1:1_av=off:er=filter:slsq=on:slsqc=0:slsqr=1,1:sp=frequency:to=lpo:i=655:si=on:rawr=on:rtra=on_0");
   quick.push("dis+34_1:32_abs=on:add=off:bsr=on:gsp=on:sp=weighted_frequency:i=940:si=on:rawr=on:rtra=on_0");
   quick.push("ott+11_4:1_br=off:fde=none:s2a=on:sd=2:sp=frequency:urr=on:i=981:si=on:rawr=on:rtra=on_0");
   quick.push("dis+22_1:128_bsd=on:rp=on:slsq=on:slsqc=1:slsqr=1,6:sp=frequency:spb=goal:thsq=on:thsqc=16:thsqd=1:thsql=off:i=90:si=on:rawr=on:rtra=on_0");
  // Improves by expected 11.014686867779822 probs costing 5327 Mi
  // Sub-schedule for 5000Mi strat cap / 40000Mi overall limit
   quick.push("dis+21_1:1_av=off:er=filter:slsq=on:slsqc=0:slsqr=1,1:sp=frequency:to=lpo:i=2016:si=on:rawr=on:rtra=on_0");
   quick.push("dis+10_1:2_atotf=0.3:i=3735:si=on:rawr=on:rtra=on_0");
   quick.push("ott+11_9:8_add=large:afp=10:amm=off:fsd=on:fsr=off:lma=on:nm=0:nwc=2.4:s2a=on:s2agt=10:sas=z3:sp=reverse_arity:tha=some:thi=overlap:i=4958:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:32_bd=off:fsr=off:newcnf=on:tgt=full:i=4959:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:1_kws=precedence:tgt=ground:i=4756:si=on:rawr=on:rtra=on_0");
   quick.push("ott+3_1:1_atotf=0.2:fsr=off:kws=precedence:sp=weighted_frequency:spb=intro:tgt=ground:i=4931:si=on:rawr=on:rtra=on_0");
   quick.push("ott+11_9:8_amm=off:bsd=on:etr=on:fsd=on:fsr=off:lma=on:newcnf=on:nm=0:nwc=3.0:s2a=on:s2agt=10:sas=z3:tha=some:i=1824:si=on:rawr=on:rtra=on_0");
   quick.push("dis+34_1:32_abs=on:add=off:bsr=on:gsp=on:sp=weighted_frequency:i=2134:si=on:rawr=on:rtra=on_0");
   quick.push("ott-1_1:1_sp=const_frequency:i=2891:si=on:rawr=on:rtra=on_0");
   quick.push("dis+2_1:64_add=large:bce=on:bd=off:i=4585:si=on:rawr=on:rtra=on_0");
   quick.push("dis+22_1:128_bsd=on:rp=on:slsq=on:slsqc=1:slsqr=1,6:sp=frequency:spb=goal:thsq=on:thsqc=16:thsqd=1:thsql=off:i=90:si=on:rawr=on:rtra=on_0");
  // Improves by expected 19.448144622151943 probs costing 36935 Mi
  // Sub-schedule for 10000Mi strat cap / 80000Mi overall limit
   quick.push("dis+21_1:1_av=off:er=filter:slsq=on:slsqc=0:slsqr=1,1:sp=frequency:to=lpo:i=2016:si=on:rawr=on:rtra=on_0");
   quick.push("dis+10_1:2_atotf=0.3:i=8004:si=on:rawr=on:rtra=on_0");
   quick.push("ott+11_9:8_add=large:afp=10:amm=off:fsd=on:fsr=off:lma=on:nm=0:nwc=2.4:s2a=on:s2agt=10:sas=z3:sp=reverse_arity:tha=some:thi=overlap:i=9965:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:32_bd=off:fsr=off:newcnf=on:tgt=full:i=9877:si=on:rawr=on:rtra=on_0");
   quick.push("ott+11_9:8_amm=off:bsd=on:etr=on:fsd=on:fsr=off:lma=on:newcnf=on:nm=0:nwc=3.0:s2a=on:s2agt=10:sas=z3:tha=some:i=1824:si=on:rawr=on:rtra=on_0");
   quick.push("dis+2_1:64_add=large:bce=on:bd=off:i=9989:si=on:rawr=on:rtra=on_0");
   quick.push("ott-11_1:32_i=9707:si=on:rawr=on:rtra=on_0");
   quick.push("dis+22_1:128_bsd=on:rp=on:slsq=on:slsqc=1:slsqr=1,6:sp=frequency:spb=goal:thsq=on:thsqc=16:thsqd=1:thsql=off:i=90:si=on:rawr=on:rtra=on_0");
  // Improves by expected 9.100420630309813 probs costing 61365 Mi
  // Sub-schedule for 50000Mi strat cap / 400000Mi overall limit
   quick.push("ott+3_1:1_abs=on:anc=none:bs=on:fsr=off:spb=goal_then_units:i=44001:si=on:rawr=on:rtra=on_0");
   quick.push("ott+11_9:8_add=large:afp=10:amm=off:fsd=on:fsr=off:lma=on:nm=0:nwc=2.4:s2a=on:s2agt=10:sas=z3:sp=reverse_arity:tha=some:thi=overlap:i=4958:si=on:rawr=on:rtra=on_0");
   quick.push("ott+1_27:428_av=off:awrs=converge:awrsf=8:bsr=unit_only:drc=off:fd=preordered:newcnf=on:nwc=1.5:skr=on:slsq=on:slsqc=2:slsql=off:slsqr=1,4:sp=reverse_frequency:uwa=one_side_constant:i=35256:si=on:rawr=on:rtra=on_0");
   quick.push("dis+1002_1:1_fde=unused:nwc=10.0:s2a=on:s2at=3.0:sac=on:i=32293:si=on:rawr=on:rtra=on_0");
   quick.push("ott+21_1:28_afr=on:anc=all_dependent:bs=on:bsr=unit_only:nicw=on:sp=const_frequency:uhcvi=on:i=37001:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:32_bd=off:fsr=off:newcnf=on:tgt=full:i=10187:si=on:rawr=on:rtra=on_0");
   quick.push("ott+3_1:1_atotf=0.2:fsr=off:kws=precedence:sp=weighted_frequency:spb=intro:tgt=ground:i=29337:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_fmbsr=2.0:nm=4:skr=on:i=38056:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_dr=on:fmbsr=2.0:newcnf=on:nm=2:i=33239:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_fmbas=predicate:gsp=on:nm=2:i=20987:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_bce=on:fmbsr=1.5:nm=4:skr=on:i=49917:si=on:rawr=on:rtra=on_0");
   quick.push("dis+2_1:64_add=large:bce=on:bd=off:i=19144:si=on:rawr=on:rtra=on_0");
   quick.push("dis+10_1:128_bd=off:lcm=predicate:sac=on:sp=reverse_arity:urr=on:i=27492:si=on:rawr=on:rtra=on_0");
   quick.push("ott-11_1:32_i=6101:si=on:rawr=on:rtra=on_0");
   quick.push("dis+22_1:128_bsd=on:rp=on:slsq=on:slsqc=1:slsqr=1,6:sp=frequency:spb=goal:thsq=on:thsqc=16:thsqd=1:thsql=off:i=90:si=on:rawr=on:rtra=on_0");
  // Improves by expected 13.362600076988887 probs costing 398190 Mi
  // Sub-schedule for 100000Mi strat cap / 800000Mi overall limit
   quick.push("ott+11_1:128_av=off:bd=off:bsr=unit_only:fd=preordered:to=lpo:updr=off:i=91600:si=on:rawr=on:rtra=on_0");
   quick.push("ott+11_9:8_add=large:afp=10:amm=off:fsd=on:fsr=off:lma=on:nm=0:nwc=2.4:s2a=on:s2agt=10:sas=z3:sp=reverse_arity:tha=some:thi=overlap:i=7127:si=on:rawr=on:rtra=on_0");
   quick.push("ott+1_27:428_av=off:awrs=converge:awrsf=8:bsr=unit_only:drc=off:fd=preordered:newcnf=on:nwc=1.5:skr=on:slsq=on:slsqc=2:slsql=off:slsqr=1,4:sp=reverse_frequency:uwa=one_side_constant:i=35256:si=on:rawr=on:rtra=on_0");
   quick.push("dis+1002_1:1_fde=unused:nwc=10.0:s2a=on:s2at=3.0:sac=on:i=32293:si=on:rawr=on:rtra=on_0");
   quick.push("ott+3_1:1_atotf=0.2:fsr=off:kws=precedence:sp=weighted_frequency:spb=intro:tgt=ground:i=29337:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_fmbsr=2.0:nm=4:skr=on:i=99860:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_fmbas=expand:i=96985:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_bce=on:dr=on:fmbsr=1.47:gsp=on:nm=2:skr=on:i=99648:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_bce=on:fmbsr=1.5:nm=4:skr=on:i=99882:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_bce=on:fmbas=predicate:fmbsr=1.5:fmbsso=preprocessed_usage:nm=4:skr=on:i=99913:si=on:rawr=on:rtra=on_0");
   quick.push("dis+10_1:128_bd=off:lcm=predicate:sac=on:sp=reverse_arity:urr=on:i=28201:si=on:rawr=on:rtra=on_0");
   quick.push("ott-11_1:32_i=9707:si=on:rawr=on:rtra=on_0");
  // Improves by expected 6.347485436212229 probs costing 729797 Mi
  // Sub-schedule for 150000Mi strat cap / 1200000Mi overall limit
   quick.push("ott+11_1:128_av=off:bd=off:bsr=unit_only:fd=preordered:to=lpo:updr=off:i=144582:si=on:rawr=on:rtra=on_0");
   quick.push("ott+1_27:428_av=off:awrs=converge:awrsf=8:bsr=unit_only:drc=off:fd=preordered:newcnf=on:nwc=1.5:skr=on:slsq=on:slsqc=2:slsql=off:slsqr=1,4:sp=reverse_frequency:uwa=one_side_constant:i=35256:si=on:rawr=on:rtra=on_0");
   quick.push("dis+1002_1:1_fde=unused:nwc=10.0:s2a=on:s2at=3.0:sac=on:i=104647:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_fmbsr=2.0:nm=4:skr=on:i=146146:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_fmbas=expand:i=112867:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_bce=on:dr=on:fmbsr=1.47:gsp=on:nm=2:skr=on:i=133500:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_fmbsr=2.0:ins=2:i=145423:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_bce=on:fmbsr=1.5:nm=4:skr=on:i=147928:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:1_bs=on:fsr=off:gs=on:i=146184:si=on:rawr=on:rtra=on_0");
  // Improves by expected 5.220673651207569 probs costing 1116524 Mi
  // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
   quick.push("ott+11_1:128_av=off:bd=off:bsr=unit_only:fd=preordered:to=lpo:updr=off:i=260001:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:1_i=496751:si=on:rawr=on:rtra=on_0");
   quick.push("ott+4_1:1_atotf=0.5:bce=on:ins=1:sp=frequency:spb=units:i=325642:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:1_kws=precedence:tgt=ground:i=480001:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_bce=on:i=479034:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_bce=on:dr=on:fmbsr=1.47:gsp=on:nm=2:skr=on:i=452948:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:1_bs=on:fsr=off:gs=on:i=262660:si=on:rawr=on:rtra=on_0");
   quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:rp=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=255558:si=on:rawr=on:rtra=on_0");
  // Improves by expected 23.026595026749764 probs costing 3012587 Mi
  // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
   quick.push("ott+11_1:128_av=off:bd=off:bsr=unit_only:fd=preordered:to=lpo:updr=off:i=260001:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:1_i=305496:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:1_kws=precedence:tgt=ground:i=480001:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_bce=on:i=467380:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_bce=on:dr=on:fmbsr=1.47:gsp=on:nm=2:skr=on:i=492000:si=on:rawr=on:rtra=on_0");
   quick.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:rp=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:i=255558:si=on:rawr=on:rtra=on_0");
  // Improves by expected 1.2113310912171895 probs costing 2260430 Mi
  // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
   quick.push("ott+10_1:1_i=496751:si=on:rawr=on:rtra=on_0");
   quick.push("ott+10_1:1_kws=precedence:tgt=ground:i=285611:si=on:rawr=on:rtra=on_0");
   quick.push("fmb+10_1:1_bce=on:dr=on:fmbsr=1.47:gsp=on:nm=2:skr=on:i=492000:si=on:rawr=on:rtra=on_0");
  // Improves by expected 0.4363593202030057 probs costing 1274359 Mi
  // Overall score 2081.1804482430707 probs on average / budget 9091993 Mi
}

void Schedules::getCascSat2023Schedule(const Property& property, Schedule& quick, Schedule& fallback)
{
  Property::Category cat = property.category();

  switch (cat) { // slowness 2.1
  case Property::FEQ:
  case Property::NEQ:
  case Property::HEQ:
  case Property::PEQ:
  case Property::UEQ:
    // total time: 6261
    quick.push("fmb+10_1_bce=on:fmbas=function:fmbsr=1.2:fde=unused:nm=0_846");
    quick.push("fmb+10_1_bce=on:fmbdsb=on:fmbes=contour:fmbswr=3:fde=none:nm=0_793");
    quick.push("dis+2_11_add=large:afr=on:amm=off:bd=off:bce=on:fsd=off:fde=none:gs=on:gsaa=full_model:gsem=off:irw=on:msp=off:nm=4:nwc=1.3:sas=z3:sims=off:sac=on:sp=reverse_arity_569");
    quick.push("fmb+10_1_bce=on:fmbsr=1.5:nm=32_533");
    quick.push("ott+10_10:1_add=off:afr=on:amm=off:anc=all:bd=off:bs=on:fsr=off:irw=on:lma=on:msp=off:nm=4:nwc=4.0:sac=on:sp=reverse_frequency_531");
    quick.push("ott-10_8_av=off:bd=preordered:bs=on:fsd=off:fsr=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=frequency_522");
    quick.push("ott+1_64_av=off:bd=off:bce=on:fsd=off:fde=unused:gsp=on:irw=on:lcm=predicate:lma=on:nm=2:nwc=1.1:sims=off:urr=on_497");
    quick.push("fmb+10_1_fmbas=expand:fmbsr=1.1:gsp=on:nm=4_411");
    quick.push("ott+1_9_av=off:bd=off:bs=on:gsp=on:lcm=predicate:nm=4:sp=weighted_frequency:urr=on_382");
    quick.push("lrs-11_2:5_fsd=off:fde=none:nm=4:nwc=5.0:sims=off:sp=reverse_weighted_frequency:stl=62_367");
    quick.push("ott+4_64_acc=on:anc=none:bs=on:bsr=on:fsd=off:gs=on:gsem=off:irw=on:msp=off:nwc=2.5:nicw=on:sims=off_354");
    quick.push("ott-11_10:1_aac=none:add=off:afr=on:amm=off:anc=all_dependent:bd=off:fsd=off:fde=none:gsp=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sas=z3:sp=occurrence_186");
    quick.push("dis-3_1_acc=on:anc=none:bd=preordered:fsd=off:fsr=off:fde=none:gs=on:gsem=on:lcm=predicate:lma=on:msp=off:nm=4:nicw=on:sims=off:sp=weighted_frequency:urr=ec_only_180");
    quick.push("dis-3_6_add=off:afr=on:amm=off:anc=none:bd=off:bs=on:bsr=on:bce=on:fsd=off:fde=none:gsp=on:gs=on:gsaa=full_model:gsem=off:sims=off:sac=on:sp=reverse_frequency_90");
    break;
    
  case Property::HNE:
  case Property::NNE:
  case Property::FNE:
  case Property::EPR:
    // total time: 3578
    quick.push("fmb+10_1_fmbas=off:fmbsr=1.3:nm=2_1451");
    quick.push("fmb+10_1_bce=on:fmbas=expand:fmbksg=on:fmbsr=1.3_569");
    quick.push("dis-2_2:3_amm=sco:anc=none:bce=on:fsr=off:gsp=on:nm=16:nwc=1.2:nicw=on:sac=on:sp=weighted_frequency_476");
    quick.push("fmb+10_1_bce=on:fmbas=expand:fmbksg=on:fmbsr=1.3:gsp=on:nm=4_470");
    quick.push("dis+1_20_av=off:lcm=predicate:nm=2:nwc=2.0_396");
    quick.push("dis+11_4:5_nm=4_216");
    break;
  }
} // getCascSat2023Schedule

void Schedules::getCasc2023Schedule(const Property& property, Schedule& quick, Schedule& fallback)
{
  unsigned atoms = property.atoms();
  Property::Category cat = property.category();
  unsigned long props = property.props();

  if (property.hasNumerals()) { // slowness 2.0
    // total time: 4971
    quick.push("lrs+2_32_add=large:amm=off:bd=off:bs=unit_only:drc=off:flr=on:fsd=off:fde=none:nm=0:nwc=1.1:sos=theory:sp=reverse_arity:tgt=ground:stl=180_1034");
    quick.push("dis-1010_2:3_canc=force:fsd=off:fde=unused:gs=on:gsem=on:nm=0:nwc=1.3:sas=z3:tha=off:thf=on:uwa=ground_572");
    quick.push("dis-10_20_canc=force:fsd=off:gs=on:gsem=off:nm=0:sas=z3:sac=on:tha=off:thi=strong:tgt=ground_476");
    quick.push("dis-11_10:1_canc=force:fsd=off:nwc=1.5:sas=z3:tha=off:uwa=all_472");
    quick.push("lrs+1010_2:1_amm=off:bs=on:bsr=on:canc=force:fsd=off:fsr=off:gs=on:gsaa=full_model:gsem=on:nm=0:nwc=1.3:sas=z3:sac=on:tha=off:thi=overlap:tgt=ground:uwa=ground:stl=60_408");
    quick.push("ott+10_1024_av=off:bd=preordered:br=off:ep=RSTC:fsr=off:fde=none:nm=2:urr=on_318");
    quick.push("lrs-1010_3_av=off:br=off:drc=off:er=known:fsd=off:fde=unused:nm=4:nwc=3.0:sp=scramble:urr=on:stl=180_280");
    quick.push("lrs-1003_28_aac=none:amm=sco:anc=none:bd=preordered:bs=on:bsr=on:drc=off:fsr=off:gsp=on:gs=on:gsaa=from_current:inw=on:nwc=1.5:sas=z3:sos=all:sac=on:sp=frequency:tha=off:uwa=all:stl=180_226");
    quick.push("lrs+1_15_bd=off:fsd=off:fde=unused:lcm=predicate:lma=on:nm=4:nwc=1.5:sos=all:sac=on:sp=occurrence:stl=60_160");
    quick.push("lrs+1011_2:1_aac=none:add=off:bs=on:bsr=on:canc=cautious:fsd=off:fsr=off:fde=none:nm=2:nwc=1.7:nicw=on:sas=z3:sp=reverse_frequency:tha=some:thf=on:thi=full:tgt=full:uwa=all:stl=60_136");
    quick.push("dis+1004_2:1_aac=none:drc=off:ep=RS:fsd=off:fde=none:gsp=on:gs=on:gsem=off:lcm=predicate:nm=2:nwc=1.2:sims=off:sos=all:sp=scramble_122");
    quick.push("dis+1004_9:1_acc=on:amm=sco:bsr=on:bce=on:drc=off:flr=on:irw=on:lma=on:msp=off:nwc=4.0:sac=on:sp=weighted_frequency_114");
    quick.push("lrs+1011_2_av=off:canc=force:drc=off:nm=4:tgt=ground:stl=60_102");
    quick.push("dis-1010_5:1_add=off:bce=on:canc=cautious:cond=fast:er=known:fsd=off:fsr=off:fde=none:inw=on:lma=on:msp=off:nwc=1.5:sas=z3:sp=reverse_frequency:tha=off:thf=on:thi=overlap:tgt=ground:urr=ec_only_90");
    quick.push("ott-1003_8:1_add=large:afr=on:amm=off:anc=all:bsr=on:flr=on:fsr=off:gs=on:lcm=predicate:nm=0:nwc=1.2:sas=z3:sos=theory:sp=scramble:thf=on:thi=strong:uwa=ground_78");
    quick.push("ott+1_10:1_amm=sco:canc=force:fsd=off:fsr=off:fde=unused:inw=on:lma=on:nm=0:nwc=1.7:sas=z3:tha=some:thi=strong:tgt=ground_58");
    quick.push("lrs+1011_4:1_canc=force:fsd=off:nwc=1.5:sas=z3:tgt=ground:stl=60_48");
    quick.push("dis+10_10:1_amm=off:bd=off:canc=cautious:fsd=off:fde=unused:sas=z3:sos=all:tha=off:uwa=interpreted_only_46");
    quick.push("ott+1002_5:1_add=off:afr=on:amm=off:bd=off:bs=unit_only:bsr=on:canc=cautious:cond=on:drc=off:fsd=off:fde=unused:irw=on:nm=64:nwc=1.5:sas=z3:sims=off:sac=on:tha=off:thi=all:uwa=all:urr=on_40");
    quick.push("lrs+11_4:1_bs=on:canc=force:drc=off:fsd=off:fsr=off:fde=unused:nwc=1.5:sas=z3:sos=theory:sac=on:sp=reverse_frequency:thf=on:thi=strong:uwa=interpreted_only:stl=60_30");
    quick.push("dis-11_4:5_add=off:bsr=on:canc=cautious:fsd=off:fsr=off:gs=on:nm=16:nwc=1.3:sas=z3:sos=on:sac=on:tgt=ground:uwa=interpreted_only:urr=ec_only_30");
    quick.push("ott-3_5:1_aac=none:amm=off:anc=all:bd=off:br=off:cond=on:er=known:lcm=reverse:nm=16:nwc=4.0:sims=off:sac=on:urr=on_26");
    quick.push("lrs+1_8:1_bd=off:bce=on:canc=force:fsd=off:fsr=off:gs=on:gsem=off:msp=off:nm=64:nwc=1.3:sas=z3:sims=off:sp=scramble:tha=off:tgt=full:urr=ec_only:stl=60_16");
    quick.push("lrs-1002_1_afr=on:drc=off:er=known:flr=on:fsd=off:gs=on:gsem=on:inw=on:irw=on:lcm=predicate:nwc=3.0:sas=z3:sac=on:sp=frequency:tha=off:stl=60_16");
    quick.push("dis+2_4:3_afr=on:anc=none:canc=force:fsd=off:nm=2:nwc=10.0:sas=z3:sos=theory:sac=on:sp=scramble:tha=off_12");
    quick.push("lrs+1002_3:1_canc=force:drc=off:fsd=off:fde=unused:gs=on:gsem=off:irw=on:nm=0:nwc=2.0:sas=z3:sos=all:tha=off:thi=full:stl=60_10");
    quick.push("lrs-10_6_aac=none:bs=on:canc=force:fsd=off:fde=none:gs=on:gsem=on:nwc=1.5:sas=z3:tha=off:tgt=ground:stl=60_8");
    quick.push("dis+1002_64_aac=none:canc=force:fsd=off:nm=4:sas=z3:sos=on:tha=off_8");
    quick.push("lrs+1002_9:1_anc=all:br=off:canc=force:drc=off:fsd=off:fde=unused:gsp=on:nwc=1.1:sas=z3:sac=on:thi=all:urr=on:stl=60_8");
    quick.push("lrs+11_4:5_bs=on:canc=cautious:fsd=off:fsr=off:gs=on:gsem=off:nm=4:sas=z3:tha=some:thf=on:thi=strong:tgt=ground:urr=on:stl=60_6");
    quick.push("lrs+4_2:3_flr=on:nm=4:nwc=10.0:sas=z3:sac=on:sp=reverse_frequency:tgt=ground:stl=60_6");
    quick.push("lrs-4_4_canc=force:drc=off:fsd=off:fsr=off:fde=none:inw=on:nm=2:nicw=on:sas=z3:sos=on:sac=on:tha=off:thf=on:uwa=all:stl=60_5");
    quick.push("lrs+11_10_afr=on:canc=force:drc=off:flr=on:fsd=off:nm=4:sas=z3:sims=off:tha=off:thi=new:uwa=one_side_constant:stl=60_4");
    quick.push("dis+10_3_canc=force:drc=off:ep=RSTC:fsd=off:fde=none:nm=4:sas=z3:sp=weighted_frequency:tha=off:urr=on_3");
    quick.push("dis+1_5:4_add=off:bs=on:bce=on:canc=cautious:gsp=on:gs=on:nm=4:nwc=2.5:sas=z3:sims=off:sos=all:sp=frequency:tha=some:thf=on:tgt=ground:uwa=one_side_interpreted_3");
    return;
  }

  switch (cat) { // slowness 2.1
  case Property::FEQ:
  case Property::NEQ:
  case Property::HEQ:
  case Property::PEQ:
    if (atoms < 30) {
      // total time: 8213
      quick.push("lrs+10_11_cond=on:drc=off:flr=on:fsr=off:gsp=on:gs=on:gsem=off:lma=on:msp=off:nm=4:nwc=1.5:nicw=on:sas=z3:sims=off:sp=scramble:stl=188_1169");
      quick.push("lrs-11_28_aac=none:afr=on:anc=none:bs=on:drc=off:fde=unused:gs=on:nm=2:nwc=1.3:sp=frequency:stl=188_1092");
      quick.push("ott-4_11_av=off:bd=preordered:bce=on:drc=off:flr=on:fsr=off:lma=on:nwc=2.0:sp=occurrence:tgt=ground:urr=ec_only_1010");
      quick.push("lrs+3_20_av=off:bd=preordered:drc=off:fsd=off:fsr=off:fde=unused:irw=on:lcm=reverse:sos=theory:stl=315_961");
      quick.push("ott+1003_4:1_av=off:cond=on:drc=off:fsd=off:fsr=off:fde=none:gsp=on:nm=2:nwc=1.5:sos=all:sp=reverse_arity:tgt=full_871");
      quick.push("lrs-11_32_av=off:bd=off:bs=on:bsr=on:drc=off:flr=on:fsd=off:fsr=off:fde=none:gsp=on:irw=on:lcm=predicate:nm=4:sp=scramble:stl=125_825");
      quick.push("ott+11_14_av=off:bs=on:bsr=on:cond=on:flr=on:fsd=off:fde=unused:gsp=on:nm=4:nwc=1.5:tgt=full_501");
      quick.push("ott+4_40_av=off:bce=on:fsd=off:fde=unused:nm=4:nwc=1.1:sos=all:sp=frequency_375");
      quick.push("lrs-11_16_av=off:bs=on:bsr=on:drc=off:fsd=off:fsr=off:nm=4:sp=scramble:tgt=ground:stl=62_367");
      quick.push("dis-1002_6_acc=on:anc=none:bce=on:cond=fast:drc=off:fsd=off:fde=none:gsp=on:irw=on:sac=on:sp=scramble:tgt=ground:urr=ec_only_237");
      quick.push("ott+10_128_aac=none:add=large:afr=on:anc=all_dependent:bsr=on:bce=on:fsd=off:irw=on:nm=2:nwc=1.5:sp=scramble:tgt=full_237");
      quick.push("ott+10_12_av=off:bs=on:bsr=on:bce=on:drc=off:fsd=off:fde=none:nm=4:nwc=1.2:sp=scramble_180");
      quick.push("lrs-3_32_aac=none:acc=on:add=off:afr=on:bsr=on:bce=on:drc=off:fsd=off:fde=unused:gsp=on:irw=on:lcm=predicate:nwc=1.3:sims=off:sp=scramble:tgt=ground:stl=62_98");
      quick.push("lrs+10_40_acc=on:add=off:afr=on:amm=off:bce=on:drc=off:fsd=off:fde=unused:gs=on:lma=on:nwc=10.0:sims=off:sp=weighted_frequency:tgt=ground:urr=on:stl=188_90");
      quick.push("dis+10_24_av=off:drc=off:fsd=off:fsr=off:nm=4:nwc=1.3:sp=occurrence:tgt=ground_79");
      quick.push("ott-10_2_av=off:fsd=off:fde=none:nm=4:nwc=1.1:sp=reverse_frequency:tgt=ground_65");
      quick.push("lrs+1010_4_aac=none:add=off:afr=on:amm=off:anc=all_dependent:bd=off:cond=on:drc=off:flr=on:fde=none:gs=on:lma=on:nm=16:nwc=1.1:sims=off:sos=all:sac=on:sp=occurrence:stl=188_56");
    }
    else if (atoms <= 130) {
      // total time: 6170
      quick.push("lrs+10_11_cond=on:drc=off:flr=on:fsr=off:gsp=on:gs=on:gsem=off:lma=on:msp=off:nm=4:nwc=1.5:nicw=on:sas=z3:sims=off:sp=scramble:stl=188_730");
      quick.push("dis+1010_4:1_anc=none:bd=off:drc=off:flr=on:fsr=off:nm=4:nwc=1.1:nicw=on:sas=z3_680");
      quick.push("dis-11_4:1_aac=none:add=off:afr=on:anc=none:bd=preordered:bs=on:bsr=on:drc=off:fsr=off:fde=none:gsp=on:irw=on:lcm=reverse:lma=on:nm=0:nwc=1.7:nicw=on:sas=z3:sims=off:sos=all:sac=on:sp=weighted_frequency:tgt=full_602");
      quick.push("lrs-3_8_anc=none:bce=on:cond=on:drc=off:flr=on:fsd=off:fsr=off:fde=unused:gsp=on:gs=on:gsaa=full_model:lcm=predicate:lma=on:nm=16:sos=all:sp=weighted_frequency:tgt=ground:urr=ec_only:stl=188_482");
      quick.push("lrs+1010_20_av=off:bd=off:bs=on:bsr=on:bce=on:flr=on:fde=none:gsp=on:nwc=3.0:tgt=ground:urr=ec_only:stl=125_424");
      quick.push("dis+1011_4_add=large:amm=off:sims=off:sac=on:sp=frequency:tgt=ground_413");
      quick.push("ott+11_14_av=off:bs=on:bsr=on:cond=on:flr=on:fsd=off:fde=unused:gsp=on:nm=4:nwc=1.5:tgt=full_386");
      quick.push("ott+10_5_av=off:bsr=on:br=off:drc=off:fsd=off:fsr=off:fde=unused:gsp=on:lcm=predicate:lma=on:nwc=2.5:sos=all:sp=occurrence:tgt=full:urr=on_375");
      quick.push("lrs-1010_3_aac=none:anc=none:er=known:fsd=off:fde=unused:gs=on:lcm=predicate:sos=on:sp=weighted_frequency:tgt=ground:stl=62_365");
      quick.push("ott+10_128_aac=none:add=large:afr=on:anc=all_dependent:bsr=on:bce=on:fsd=off:irw=on:nm=2:nwc=1.5:sp=scramble:tgt=full_251");
      quick.push("lrs-1010_2_av=off:bce=on:cond=on:er=filter:fde=unused:lcm=predicate:nm=2:nwc=3.0:sims=off:sp=frequency:urr=on:stl=188_224");
      quick.push("lrs+1002_1024_bce=on:er=known:fsd=off:fsr=off:gsp=on:nm=32:tgt=ground:stl=62_188");
      quick.push("dis-2_3:4_bd=off:bs=on:br=off:fsd=off:fde=none:nm=0:nwc=1.1:sas=z3:urr=on_186");
      quick.push("ott-3_10:1_add=off:amm=off:bd=off:bsr=on:bce=on:cond=on:er=known:gs=on:lcm=reverse:lma=on:msp=off:nm=0:nwc=1.3:nicw=on:sas=z3:sims=off:sac=on:sp=reverse_weighted_frequency:urr=on_178");
      quick.push("ott-10_4:3_add=off:bd=off:br=off:fsd=off:fde=none:irw=on:nwc=2.5:sas=z3:sims=off:sos=all:sac=on:sp=scramble:urr=on_117");
      quick.push("lrs+10_40_acc=on:add=off:afr=on:amm=off:bce=on:drc=off:fsd=off:fde=unused:gs=on:lma=on:nwc=10.0:sims=off:sp=weighted_frequency:tgt=ground:urr=on:stl=188_75");
      quick.push("ott+11_50_av=off:bd=off:bs=on:cond=on:fsd=off:fsr=off:nm=0:nwc=2.0:sos=theory:sp=reverse_frequency:tgt=ground_71");
      quick.push("dis-1004_2_av=off:fsd=off:gsp=on:nm=4:nwc=1.5:sp=reverse_frequency:tgt=ground_65");
      quick.push("lrs+1011_2_bce=on:drc=off:nm=4:nwc=1.2:sac=on:sp=occurrence:urr=on:stl=62_54");
      quick.push("dis+1002_2:5_av=off:fsd=off:fde=none:nm=4:nwc=1.7:sims=off:sos=all:sp=scramble:tgt=ground_52");
      quick.push("ott+11_8:1_aac=none:amm=sco:anc=none:er=known:flr=on:fde=unused:irw=on:nm=0:nwc=1.2:nicw=on:sims=off:sos=all:sac=on_46");
      quick.push("lrs+1011_2:5_bs=unit_only:fsd=off:fde=none:nm=4:nwc=5.0:sac=on:stl=62_44");
      quick.push("lrs+1011_7_aac=none:add=off:afr=on:anc=none:bs=unit_only:bsr=on:fsd=off:fsr=off:fde=none:gs=on:nm=2:nwc=1.5:sp=occurrence:urr=on:stl=62_39");
      quick.push("dis-1010_2:5_av=off:bd=off:fsd=off:fde=none:nm=4:sos=on:sp=occurrence_23");
      quick.push("lrs+1010_5:1_bd=off:fsd=off:fde=unused:lcm=predicate:nm=64:nwc=1.7:sac=on:sp=frequency:tgt=ground:stl=62_23");
      quick.push("ott+1010_2:5_bd=off:fsd=off:fde=none:nm=16:sos=on_16");
      quick.push("lrs+1011_2:5_aac=none:anc=all_dependent:fsr=off:gsp=on:irw=on:lcm=predicate:nm=0:nwc=5.0:sims=off:tgt=ground:stl=62_10");
      quick.push("dis+11_9:1_aac=none:drc=off:fsd=off:fde=none:lcm=predicate:nm=2:sas=z3:sos=on:urr=on_8");
      quick.push("dis+1011_9:1_ep=RS:fsd=off:fde=unused:nm=4:nwc=4.0:sos=all_8");
      quick.push("lrs-2_5_fsd=off:gsp=on:nm=0:nwc=5.0:sims=off:tgt=ground:stl=62_6");
      quick.push("ott+1_1_av=off:drc=off:fsd=off:lcm=predicate:sp=scramble:tgt=full_5");
      quick.push("ott+1011_4_er=known:fsd=off:nm=4:tgt=ground_5");
      quick.push("ott+1002_5:1_fsd=off:gs=on:gsem=off:nwc=2.5:urr=on_4");
      quick.push("ott-1003_24_aac=none:gsp=on:nm=2:sos=all:urr=on_4");
      quick.push("ott-1002_4:5_flr=on:fsd=off:fsr=off:fde=unused:nm=2:nwc=4.0:sac=on_4");
      quick.push("dis+1011_2:1_add=off:afr=on:er=known:fde=unused:nwc=1.3:nicw=on:sas=z3:sims=off:sos=on:sac=on:tgt=full_4");
      quick.push("lrs+10_5:4_amm=off:bsr=on:drc=off:ep=R:er=known:flr=on:gsp=on:gs=on:irw=on:lcm=predicate:lma=on:msp=off:nm=0:nwc=1.5:sas=z3:sos=on:sp=weighted_frequency:stl=62_3");
    }
    else if (atoms <= 250) {
      // total time: 7148
      quick.push("lrs+1010_20_av=off:bd=off:bs=on:bsr=on:bce=on:flr=on:fde=none:gsp=on:nwc=3.0:tgt=ground:urr=ec_only:stl=125_1192");
      quick.push("ott+3_2:7_add=large:amm=off:anc=all:bce=on:drc=off:fsd=off:fde=unused:gs=on:irw=on:lcm=predicate:lma=on:msp=off:nwc=10.0:sac=on_598");
      quick.push("lrs+11_10:1_bs=unit_only:drc=off:fsd=off:fde=none:gs=on:msp=off:nm=16:nwc=2.0:nicw=on:sos=all:sac=on:sp=reverse_frequency:stl=62_575");
      quick.push("lrs+2_5:4_anc=none:br=off:fde=unused:gsp=on:nm=32:nwc=1.3:sims=off:sos=all:urr=on:stl=62_558");
      quick.push("lrs-1010_20_afr=on:anc=all_dependent:bs=on:bsr=on:cond=on:er=known:fde=none:nm=4:nwc=1.3:sims=off:sp=frequency:urr=on:stl=62_533");
      quick.push("lrs-1010_2_av=off:bce=on:cond=on:er=filter:fde=unused:lcm=predicate:nm=2:nwc=3.0:sims=off:sp=frequency:urr=on:stl=188_520");
      quick.push("ott+1010_1_aac=none:bce=on:ep=RS:fsd=off:nm=4:nwc=2.0:nicw=on:sas=z3:sims=off_453");
      quick.push("dis+1011_4_add=large:amm=off:sims=off:sac=on:sp=frequency:tgt=ground_401");
      quick.push("lrs+1010_4_aac=none:add=off:afr=on:amm=off:anc=all_dependent:bd=off:cond=on:drc=off:flr=on:fde=none:gs=on:lma=on:nm=16:nwc=1.1:sims=off:sos=all:sac=on:sp=occurrence:stl=188_398");
      quick.push("dis-1010_1_fsd=off:fsr=off:fde=none:nm=4:sos=all:urr=ec_only_245");
      quick.push("lrs+1011_2:5_bs=unit_only:fsd=off:fde=none:nm=4:nwc=5.0:sac=on:stl=62_239");
      quick.push("lrs+1010_5:1_bd=off:fsd=off:fde=unused:lcm=predicate:nm=64:nwc=1.7:sac=on:sp=frequency:tgt=ground:stl=62_151");
      quick.push("lrs+1010_9:1_aac=none:anc=all_dependent:bd=off:bsr=on:bce=on:er=filter:fsd=off:fde=unused:gs=on:gsem=on:lcm=predicate:lma=on:nm=4:nwc=5.0:sims=off:sos=all:sp=occurrence:stl=62_151");
      quick.push("ott+1002_5:1_fsd=off:gs=on:gsem=off:nwc=2.5:urr=on_136");
      quick.push("dis+1011_5_aac=none:acc=on:add=off:amm=off:anc=all:bd=off:bs=on:bsr=on:er=filter:flr=on:fde=unused:gsp=on:lma=on:msp=off:nm=4:nwc=3.0:nicw=on:sos=theory:sp=scramble:tgt=ground:urr=ec_only_134");
      quick.push("ott-1010_2:3_av=off:bd=off:bs=on:bsr=on:cond=fast:drc=off:er=filter:fsd=off:fde=none:gsp=on:irw=on:lcm=reverse:nm=16:nwc=3.0:sims=off:sp=weighted_frequency:urr=ec_only_119");
      quick.push("lrs+4_32_add=off:bs=unit_only:bsr=on:fde=none:nm=4:sas=z3:urr=ec_only:stl=62_107");
      quick.push("dis-1002_6_acc=on:anc=none:bce=on:cond=fast:drc=off:fsd=off:fde=none:gsp=on:irw=on:sac=on:sp=scramble:tgt=ground:urr=ec_only_104");
      quick.push("lrs+1_9:1_aac=none:amm=off:ep=RST:fsd=off:fde=unused:gs=on:sos=all:sac=on:sp=frequency:urr=on:stl=62_100");
      quick.push("ott+11_2:5_anc=all_dependent:bs=on:bsr=on:drc=off:fsd=off:fsr=off:lcm=reverse:lma=on:nm=4:sos=theory:sp=frequency_65");
      quick.push("dis+1011_2:1_add=off:afr=on:er=known:fde=unused:nwc=1.3:nicw=on:sas=z3:sims=off:sos=on:sac=on:tgt=full_65");
      quick.push("lrs+10_5:4_amm=off:bsr=on:drc=off:ep=R:er=known:flr=on:gsp=on:gs=on:irw=on:lcm=predicate:lma=on:msp=off:nm=0:nwc=1.5:sas=z3:sos=on:sp=weighted_frequency:stl=62_60");
      quick.push("dis-4_5:1_av=off:bd=off:drc=off:fsd=off:fde=unused:irw=on:lcm=reverse:lma=on:nwc=3.0:sos=all:sp=weighted_frequency_56");
      quick.push("dis+3_3:2_aac=none:fsd=off:fde=none:lcm=reverse:nm=32:nicw=on:sos=on:sac=on:sp=occurrence_48");
      quick.push("lrs+1002_3:4_add=off:ep=RST:fsd=off:fde=none:gs=on:sos=on:sp=scramble:stl=62_31");
      quick.push("dis-1002_1_bd=off:fsd=off:fsr=off:fde=none:nwc=1.3:sims=off:sos=all_29");
      quick.push("dis+1_2:7_add=off:afr=on:amm=off:bd=off:cond=on:er=known:fsd=off:fde=unused:gsp=on:lcm=predicate:nwc=4.0:nicw=on:sos=on:sac=on:sp=occurrence:tgt=ground_21");
      quick.push("ott+11_4:1_av=off:bd=preordered:bsr=on:drc=off:fsd=off:fde=unused:gsp=on:nm=4:nwc=1.1:sp=scramble_18");
      quick.push("ott+1002_2:5_acc=on:bd=preordered:bsr=on:er=known:flr=on:fsd=off:fde=none:msp=off:nm=64:sos=on:sac=on:sp=reverse_frequency_12");
      quick.push("dis-2_3:4_bd=off:bs=on:br=off:fsd=off:fde=none:nm=0:nwc=1.1:sas=z3:urr=on_8");
      quick.push("ott+10_12_av=off:bs=on:bsr=on:bce=on:drc=off:fsd=off:fde=none:nm=4:nwc=1.2:sp=scramble_6");
      quick.push("dis+1011_3_av=off:bd=off:er=known:fsd=off:fde=unused:irw=on:nm=64:nwc=1.3:sos=on:sp=reverse_arity_5");
      quick.push("lrs+10_3:4_br=off:bce=on:fsd=off:nm=0:sos=on:sp=occurrence:urr=on:stl=62_4");
      quick.push("ott+1010_2:5_bd=off:fsd=off:fde=none:nm=16:sos=on_3");
      quick.push("dis+1011_2:3_av=off:cond=on:ep=RS:flr=on:fsd=off:lcm=reverse:nm=0:nwc=2.5:sp=frequency_3");
    }
    else if (atoms <= 1300) {
      // total time: 6944
      quick.push("lrs+1011_1_bd=preordered:flr=on:fsd=off:fsr=off:irw=on:lcm=reverse:msp=off:nm=2:nwc=10.0:sos=on:sp=reverse_weighted_frequency:tgt=full:stl=62_562");
      quick.push("lrs-1004_3_av=off:ep=RSTC:fsd=off:fsr=off:urr=ec_only:stl=62_525");
      quick.push("lrs+10_4:5_amm=off:bsr=on:bce=on:flr=on:fsd=off:fde=unused:gs=on:gsem=on:lcm=predicate:sos=all:tgt=ground:stl=62_514");
      quick.push("ott+1011_4_er=known:fsd=off:nm=4:tgt=ground_499");
      quick.push("ott+11_8:1_aac=none:amm=sco:anc=none:er=known:flr=on:fde=unused:irw=on:nm=0:nwc=1.2:nicw=on:sims=off:sos=all:sac=on_470");
      quick.push("lrs+10_1024_av=off:bsr=on:br=off:ep=RSTC:fsd=off:irw=on:nm=4:nwc=1.1:sims=off:urr=on:stl=125_440");
      quick.push("ott+1010_2:5_bd=off:fsd=off:fde=none:nm=16:sos=on_419");
      quick.push("lrs-11_32_amm=off:bce=on:cond=on:er=filter:fsd=off:fde=none:gs=on:gsem=on:lcm=reverse:nm=4:nwc=1.1:sos=all:sac=on:sp=frequency:urr=on:stl=125_403");
      quick.push("lrs+1010_5:1_bd=off:fsd=off:fde=unused:lcm=predicate:nm=64:nwc=1.7:sac=on:sp=frequency:tgt=ground:stl=62_333");
      quick.push("dis+1011_4_add=large:amm=off:sims=off:sac=on:sp=frequency:tgt=ground_256");
      quick.push("lrs+10_7_av=off:bd=preordered:bs=on:ep=RS:fsd=off:irw=on:nm=4:nwc=1.2:sos=all:tgt=full:urr=ec_only:stl=62_251");
      quick.push("ott+1010_3_aac=none:bs=unit_only:bce=on:ep=R:er=filter:fsd=off:fde=none:gsp=on:irw=on:lcm=predicate:nwc=10.0:sos=all:sp=occurrence_243");
      quick.push("dis+1003_2:3_add=off:amm=sco:anc=all_dependent:bd=off:bce=on:drc=off:fsd=off:fde=none:gsp=on:irw=on:nm=0:nwc=2.5:nicw=on:sims=off:sac=on:sp=reverse_frequency:tgt=full_216");
      quick.push("ott+1002_2:5_acc=on:bd=preordered:bsr=on:er=known:flr=on:fsd=off:fde=none:msp=off:nm=64:sos=on:sac=on:sp=reverse_frequency_212");
      quick.push("lrs+1002_1024_bce=on:er=known:fsd=off:fsr=off:gsp=on:nm=32:tgt=ground:stl=62_207");
      quick.push("lrs+1010_4_aac=none:add=off:afr=on:amm=off:anc=all_dependent:bd=off:cond=on:drc=off:flr=on:fde=none:gs=on:lma=on:nm=16:nwc=1.1:sims=off:sos=all:sac=on:sp=occurrence:stl=188_149");
      quick.push("ott-1010_2:3_av=off:bd=off:bs=on:bsr=on:cond=fast:drc=off:er=filter:fsd=off:fde=none:gsp=on:irw=on:lcm=reverse:nm=16:nwc=3.0:sims=off:sp=weighted_frequency:urr=ec_only_149");
      quick.push("dis+1011_2:3_av=off:cond=on:ep=RS:flr=on:fsd=off:lcm=reverse:nm=0:nwc=2.5:sp=frequency_140");
      quick.push("ott+1010_1_aac=none:bce=on:ep=RS:fsd=off:nm=4:nwc=2.0:nicw=on:sas=z3:sims=off_123");
      quick.push("lrs+1011_2:5_bs=unit_only:fsd=off:fde=none:nm=4:nwc=5.0:sac=on:stl=62_115");
      quick.push("ott+1011_2_aac=none:bsr=on:ep=R:fsd=off:fde=unused:nm=16:nwc=1.5:sas=z3:sos=on_107");
      quick.push("lrs-2_2_aac=none:afr=on:anc=all_dependent:bd=off:drc=off:er=filter:fsd=off:fde=none:gs=on:irw=on:nm=4:nwc=2.5:sims=off:sos=on:sp=scramble:stl=62_104");
      quick.push("lrs+1010_20_av=off:bd=off:bs=on:bsr=on:bce=on:flr=on:fde=none:gsp=on:nwc=3.0:tgt=ground:urr=ec_only:stl=125_96");
      quick.push("dis+11_9:1_aac=none:drc=off:fsd=off:fde=none:lcm=predicate:nm=2:sas=z3:sos=on:urr=on_94");
      quick.push("lrs+4_2:3_bd=preordered:bce=on:fsd=off:fde=unused:lma=on:nm=32:nwc=1.3:sims=off:sos=all:sp=reverse_frequency:stl=62_77");
      quick.push("ott+11_1_fsd=off:fde=unused:lcm=reverse:nm=0:sas=z3:sims=off:sos=on:sp=weighted_frequency_42");
      quick.push("lrs+1010_1_amm=off:bs=on:bsr=on:fsd=off:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:nm=0:sos=on:sac=on:urr=ec_only:stl=62_39");
      quick.push("ott+1002_5:1_fsd=off:gs=on:gsem=off:nwc=2.5:urr=on_29");
      quick.push("dis+10_2_gsp=on:gs=on:gsem=off:nm=2_27");
      quick.push("dis+1011_3_av=off:bd=off:er=known:fsd=off:fde=unused:irw=on:nm=64:nwc=1.3:sos=on:sp=reverse_arity_23");
      quick.push("dis+3_3:2_aac=none:fsd=off:fde=none:lcm=reverse:nm=32:nicw=on:sos=on:sac=on:sp=occurrence_21");
      quick.push("dis-1010_4:3_afr=on:amm=off:bsr=on:bce=on:drc=off:fsd=off:fde=unused:gs=on:gsaa=from_current:irw=on:nwc=1.3:nicw=on:sas=z3:tgt=full:urr=ec_only_10");
      quick.push("lrs+1010_15_av=off:bd=off:bce=on:er=known:fsr=off:nm=16:nwc=2.0:sp=frequency:tgt=ground:urr=ec_only:stl=62_10");
      quick.push("dis+1011_2:1_add=off:afr=on:er=known:fde=unused:nwc=1.3:nicw=on:sas=z3:sims=off:sos=on:sac=on:tgt=full_10");
      quick.push("lrs+4_2:1_anc=none:bd=off:er=known:fsd=off:fsr=off:irw=on:lma=on:nm=16:nicw=on:sos=all:stl=62_6");
      quick.push("ott+3_2:7_add=large:amm=off:anc=all:bce=on:drc=off:fsd=off:fde=unused:gs=on:irw=on:lcm=predicate:lma=on:msp=off:nwc=10.0:sac=on_6");
      quick.push("lrs+11_1_amm=sco:anc=all:bs=unit_only:flr=on:fsd=off:fde=none:gsp=on:nm=4:sims=off:sos=all:sp=reverse_frequency:stl=62_6");
      quick.push("lrs+10_3:4_br=off:bce=on:fsd=off:nm=0:sos=on:sp=occurrence:urr=on:stl=62_5");
      quick.push("ott-1002_4:5_flr=on:fsd=off:fsr=off:fde=unused:nm=2:nwc=4.0:sac=on_3");
      quick.push("lrs-2_5_fsd=off:gsp=on:nm=0:nwc=5.0:sims=off:tgt=ground:stl=62_3");
    }
    else if (atoms <= 5000) {
      // total time: 7840
      quick.push("lrs-1010_2_av=off:bce=on:cond=on:er=filter:fde=unused:lcm=predicate:nm=2:nwc=3.0:sims=off:sp=frequency:urr=on:stl=188_1064");
      quick.push("dis+1010_4:1_anc=none:bd=off:drc=off:flr=on:fsr=off:nm=4:nwc=1.1:nicw=on:sas=z3_957");
      quick.push("lrs+1010_4_aac=none:add=off:afr=on:amm=off:anc=all_dependent:bd=off:cond=on:drc=off:flr=on:fde=none:gs=on:lma=on:nm=16:nwc=1.1:sims=off:sos=all:sac=on:sp=occurrence:stl=188_669");
      quick.push("dis-1010_4:3_afr=on:amm=off:bsr=on:bce=on:drc=off:fsd=off:fde=unused:gs=on:gsaa=from_current:irw=on:nwc=1.3:nicw=on:sas=z3:tgt=full:urr=ec_only_619");
      quick.push("lrs+1002_9_av=off:bs=on:bsr=on:bce=on:cond=on:drc=off:er=filter:flr=on:fsd=off:fsr=off:fde=unused:lcm=predicate:nm=2:nwc=1.3:sims=off:stl=62_466");
      quick.push("ott+10_8_br=off:cond=on:fsr=off:gsp=on:nm=16:nwc=3.0:sims=off:sp=reverse_frequency:urr=on_432");
      quick.push("dis+1011_3:2_av=off:ep=RST:fsd=off:fde=none:gsp=on:nm=2:nwc=2.0:sos=on:sp=reverse_frequency_405");
      quick.push("dis-1002_6_acc=on:anc=none:bce=on:cond=fast:drc=off:fsd=off:fde=none:gsp=on:irw=on:sac=on:sp=scramble:tgt=ground:urr=ec_only_401");
      quick.push("ott+1002_5:1_fsd=off:gs=on:gsem=off:nwc=2.5:urr=on_384");
      quick.push("ott-1010_1_add=off:afr=on:amm=off:bsr=on:bce=on:er=known:flr=on:fde=none:gsp=on:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.2:nicw=on:sas=z3:sos=on:sac=on:urr=on_354");
      quick.push("lrs+1010_5:1_bd=off:fsd=off:fde=unused:lcm=predicate:nm=64:nwc=1.7:sac=on:sp=frequency:tgt=ground:stl=62_346");
      quick.push("lrs+10_1024_av=off:bsr=on:br=off:ep=RSTC:fsd=off:irw=on:nm=4:nwc=1.1:sims=off:urr=on:stl=125_294");
      quick.push("ott+10_8:1_br=off:cond=on:ep=RSTC:fsd=off:nm=0:sos=all:sp=reverse_weighted_frequency:tgt=full:urr=on_264");
      quick.push("dis+1011_4_add=large:amm=off:sims=off:sac=on:sp=frequency:tgt=ground_195");
      quick.push("dis+1011_2:3_av=off:cond=on:ep=RS:flr=on:fsd=off:lcm=reverse:nm=0:nwc=2.5:sp=frequency_136");
      quick.push("lrs-11_3:4_add=off:anc=none:bs=on:drc=off:flr=on:fsd=off:fsr=off:fde=none:gsp=on:gs=on:gsem=off:lcm=predicate:nm=4:sas=z3:sos=all:sp=scramble:urr=ec_only:stl=62_121");
      quick.push("lrs+1011_2:5_bs=unit_only:fsd=off:fde=none:nm=4:nwc=5.0:sac=on:stl=62_115");
      quick.push("lrs+1011_2:3_av=off:fsd=off:fsr=off:fde=unused:nwc=2.0:stl=62_86");
      quick.push("lrs+1_9:1_aac=none:amm=off:ep=RST:fsd=off:fde=unused:gs=on:sos=all:sac=on:sp=frequency:urr=on:stl=62_77");
      quick.push("dis-1002_1_bd=off:fsd=off:fsr=off:fde=none:nwc=1.3:sims=off:sos=all_62");
      quick.push("lrs+11_4:3_aac=none:add=off:amm=off:anc=none:bd=preordered:bs=on:bce=on:flr=on:fsd=off:fsr=off:fde=none:nwc=2.5:sims=off:sp=reverse_arity:tgt=full:stl=188_54");
      quick.push("ott+1002_2:5_acc=on:bd=preordered:bsr=on:er=known:flr=on:fsd=off:fde=none:msp=off:nm=64:sos=on:sac=on:sp=reverse_frequency_46");
      quick.push("dis-11_9_av=off:cond=fast:ep=RST:er=known:flr=on:fsd=off:fde=unused:gsp=on:nm=16:sp=reverse_arity:urr=ec_only_46");
      quick.push("ott+3_2:7_add=large:amm=off:anc=all:bce=on:drc=off:fsd=off:fde=unused:gs=on:irw=on:lcm=predicate:lma=on:msp=off:nwc=10.0:sac=on_33");
      quick.push("dis+1011_4:3_av=off:bd=preordered:drc=off:fsd=off:fde=none:nm=4:nwc=10.0_31");
      quick.push("lrs-2_2_aac=none:afr=on:anc=all_dependent:bd=off:drc=off:er=filter:fsd=off:fde=none:gs=on:irw=on:nm=4:nwc=2.5:sims=off:sos=on:sp=scramble:stl=62_31");
      quick.push("lrs+10_7_av=off:fsd=off:fde=unused:lcm=predicate:nm=0:nwc=2.0:sp=frequency:urr=on:stl=62_29");
      quick.push("dis-10_2:3_anc=none:bd=off:bsr=on:bce=on:cond=on:fsd=off:fde=unused:lcm=predicate:lma=on:msp=off:nm=16:nwc=1.5:sos=on:sac=on:sp=reverse_frequency_27");
      quick.push("lrs+1011_1_bd=preordered:flr=on:fsd=off:fsr=off:irw=on:lcm=reverse:msp=off:nm=2:nwc=10.0:sos=on:sp=reverse_weighted_frequency:tgt=full:stl=62_23");
      quick.push("lrs+1010_9:1_aac=none:anc=all_dependent:bd=off:bsr=on:bce=on:er=filter:fsd=off:fde=unused:gs=on:gsem=on:lcm=predicate:lma=on:nm=4:nwc=5.0:sims=off:sos=all:sp=occurrence:stl=62_16");
      quick.push("dis+1004_20_av=off:fsd=off:fsr=off:gsp=on:nm=0:nwc=1.5_14");
      quick.push("ott+11_6_add=off:afr=on:amm=sco:flr=on:fsd=off:fde=none:lcm=predicate:nm=4:sims=off:sac=on:sp=frequency:urr=ec_only_8");
      quick.push("ott+11_8:1_aac=none:amm=sco:anc=none:er=known:flr=on:fde=unused:irw=on:nm=0:nwc=1.2:nicw=on:sims=off:sos=all:sac=on_8");
      quick.push("ott-4_3:4_ep=RSTC:fsd=off:lcm=predicate:nm=4:nwc=1.3:nicw=on:sims=off:sos=on:sac=on_8");
      quick.push("ott+1011_2_aac=none:bsr=on:ep=R:fsd=off:fde=unused:nm=16:nwc=1.5:sas=z3:sos=on_6");
      quick.push("lrs+1011_2_av=off:bs=on:flr=on:fsd=off:fsr=off:fde=none:lcm=predicate:nm=0:nwc=5.0:sp=reverse_arity:stl=62_6");
      quick.push("ott-10_4:3_add=off:bd=off:br=off:fsd=off:fde=none:irw=on:nwc=2.5:sas=z3:sims=off:sos=all:sac=on:sp=scramble:urr=on_4");
      quick.push("dis-1010_2:5_av=off:bd=off:fsd=off:fde=none:nm=4:sos=on:sp=occurrence_3");
    }
    else if (atoms <= 16000) {
      // total time: 6707
      quick.push("dis+1011_3_av=off:bd=off:er=known:fsd=off:fde=unused:irw=on:nm=64:nwc=1.3:sos=on:sp=reverse_arity_577");
      quick.push("dis-1002_1_bd=off:fsd=off:fsr=off:fde=none:nwc=1.3:sims=off:sos=all_501");
      quick.push("ott-11_3:1_afr=on:anc=all_dependent:bd=preordered:bce=on:er=filter:fsd=off:fde=unused:nm=4:sos=all:sac=on:tgt=full:urr=on_476");
      quick.push("ott+1010_3_aac=none:bs=unit_only:bce=on:ep=R:er=filter:fsd=off:fde=none:gsp=on:irw=on:lcm=predicate:nwc=10.0:sos=all:sp=occurrence_449");
      quick.push("dis+3_3:2_aac=none:fsd=off:fde=none:lcm=reverse:nm=32:nicw=on:sos=on:sac=on:sp=occurrence_419");
      quick.push("dis+1011_2:1_add=off:afr=on:er=known:fde=unused:nwc=1.3:nicw=on:sas=z3:sims=off:sos=on:sac=on:tgt=full_398");
      quick.push("dis+1011_4_add=large:amm=off:sims=off:sac=on:sp=frequency:tgt=ground_394");
      quick.push("lrs+1010_5:1_bd=off:fsd=off:fde=unused:lcm=predicate:nm=64:nwc=1.7:sac=on:sp=frequency:tgt=ground:stl=62_392");
      quick.push("dis+1011_3:2_av=off:ep=RST:fsd=off:fde=none:gsp=on:nm=2:nwc=2.0:sos=on:sp=reverse_frequency_373");
      quick.push("lrs+1011_2_av=off:bs=on:flr=on:fsd=off:fsr=off:fde=none:lcm=predicate:nm=0:nwc=5.0:sp=reverse_arity:stl=62_323");
      quick.push("lrs-1_4:5_av=off:bd=off:bsr=on:fsd=off:lcm=predicate:nm=4:sos=on:stl=62_310");
      quick.push("ott+11_3:4_av=off:bs=on:cond=on:drc=off:flr=on:fsd=off:fde=unused:gsp=on:lcm=predicate:nm=2:nwc=2.0:sos=on:sp=occurrence:urr=ec_only_304");
      quick.push("dis-1010_2:5_av=off:bd=off:fsd=off:fde=none:nm=4:sos=on:sp=occurrence_291");
      quick.push("ott+4_40_av=off:bce=on:fsd=off:fde=unused:nm=4:nwc=1.1:sos=all:sp=frequency_268");
      quick.push("dis-4_5:1_av=off:bd=off:drc=off:fsd=off:fde=unused:irw=on:lcm=reverse:lma=on:nwc=3.0:sos=all:sp=weighted_frequency_249");
      quick.push("ott+1010_2:5_bd=off:fsd=off:fde=none:nm=16:sos=on_241");
      quick.push("lrs+11_10:1_bs=unit_only:drc=off:fsd=off:fde=none:gs=on:msp=off:nm=16:nwc=2.0:nicw=on:sos=all:sac=on:sp=reverse_frequency:stl=62_172");
      quick.push("ott+11_4:5_anc=all:bd=preordered:cond=on:fsd=off:gs=on:lcm=predicate:nm=16:nwc=2.0:sims=off:sac=on:sp=reverse_frequency_172");
      quick.push("lrs+1002_3:4_add=off:ep=RST:fsd=off:fde=none:gs=on:sos=on:sp=scramble:stl=62_153");
      quick.push("dis+1011_4:3_av=off:bd=preordered:drc=off:fsd=off:fde=none:nm=4:nwc=10.0_81");
      quick.push("lrs-11_32_amm=off:bce=on:cond=on:er=filter:fsd=off:fde=none:gs=on:gsem=on:lcm=reverse:nm=4:nwc=1.1:sos=all:sac=on:sp=frequency:urr=on:stl=125_67");
      quick.push("lrs+1002_1_aac=none:amm=off:anc=all_dependent:ep=RS:fsd=off:fsr=off:lcm=predicate:nm=16:nwc=1.2:nicw=on:sas=z3:sos=on:stl=62_44");
      quick.push("lrs+1_9:1_aac=none:amm=off:ep=RST:fsd=off:fde=unused:gs=on:sos=all:sac=on:sp=frequency:urr=on:stl=62_16");
      quick.push("lrs+3_20_av=off:bd=preordered:drc=off:fsd=off:fsr=off:fde=unused:irw=on:lcm=reverse:sos=theory:stl=315_16");
      quick.push("dis+1_2:7_add=off:afr=on:amm=off:bd=off:cond=on:er=known:fsd=off:fde=unused:gsp=on:lcm=predicate:nwc=4.0:nicw=on:sos=on:sac=on:sp=occurrence:tgt=ground_16");
      quick.push("ott+1002_2:5_acc=on:bd=preordered:bsr=on:er=known:flr=on:fsd=off:fde=none:msp=off:nm=64:sos=on:sac=on:sp=reverse_frequency_5");
    }
    else if (atoms <= 50000) {
      // total time: 7782
      quick.push("lrs+1_11_av=off:bd=preordered:bsr=on:bce=on:cond=on:fsd=off:fde=none:lcm=predicate:nm=4:nwc=1.5:sims=off:sos=all:sp=reverse_arity:stl=188_848");
      quick.push("lrs+11_10:1_bs=unit_only:drc=off:fsd=off:fde=none:gs=on:msp=off:nm=16:nwc=2.0:nicw=on:sos=all:sac=on:sp=reverse_frequency:stl=62_623");
      quick.push("lrs+1010_5:1_bd=off:fsd=off:fde=unused:lcm=predicate:nm=64:nwc=1.7:sac=on:sp=frequency:tgt=ground:stl=62_615");
      quick.push("dis-4_5:1_av=off:bd=off:drc=off:fsd=off:fde=unused:irw=on:lcm=reverse:lma=on:nwc=3.0:sos=all:sp=weighted_frequency_613");
      quick.push("lrs+1010_15_av=off:bd=off:bce=on:er=known:fsr=off:nm=16:nwc=2.0:sp=frequency:tgt=ground:urr=ec_only:stl=62_527");
      quick.push("dis+2_5:1_av=off:bsr=on:bce=on:er=known:fde=unused:lcm=reverse:nm=2:nwc=5.0:sp=frequency:tgt=full_489");
      quick.push("dis+1011_3:2_av=off:ep=RST:fsd=off:fde=none:gsp=on:nm=2:nwc=2.0:sos=on:sp=reverse_frequency_445");
      quick.push("dis-1010_2:5_av=off:bd=off:fsd=off:fde=none:nm=4:sos=on:sp=occurrence_415");
      quick.push("ott+11_14_av=off:bs=on:bsr=on:cond=on:flr=on:fsd=off:fde=unused:gsp=on:nm=4:nwc=1.5:tgt=full_398");
      quick.push("dis+1010_2:3_aac=none:amm=sco:anc=all:bce=on:flr=on:fsr=off:gs=on:nm=16:nwc=10.0:sp=occurrence:urr=on_279");
      quick.push("dis+1011_4_add=large:amm=off:sims=off:sac=on:sp=frequency:tgt=ground_262");
      quick.push("ott+1_24_aac=none:acc=on:amm=off:bs=unit_only:bce=on:fsr=off:fde=unused:irw=on:lcm=reverse:msp=off:nm=4:nwc=10.0:nicw=on:sims=off:sos=all:sp=frequency:tgt=ground_226");
      quick.push("ott+1010_2:5_bd=off:fsd=off:fde=none:nm=16:sos=on_205");
      quick.push("dis+1011_2:1_add=off:afr=on:er=known:fde=unused:nwc=1.3:nicw=on:sas=z3:sims=off:sos=on:sac=on:tgt=full_201");
      quick.push("ott+1002_5:1_fsd=off:gs=on:gsem=off:nwc=2.5:urr=on_172");
      quick.push("lrs+1003_3:2_aac=none:afr=on:amm=off:bs=on:bce=on:cond=on:drc=off:fsr=off:gs=on:gsem=off:irw=on:lcm=predicate:nm=4:nwc=2.0:sims=off:sos=on:sac=on:sp=scramble:stl=188_157");
      quick.push("lrs+1002_1024_bce=on:er=known:fsd=off:fsr=off:gsp=on:nm=32:tgt=ground:stl=62_155");
      quick.push("dis+1011_3_av=off:bd=off:er=known:fsd=off:fde=unused:irw=on:nm=64:nwc=1.3:sos=on:sp=reverse_arity_130");
      quick.push("lrs-1010_20_afr=on:anc=all_dependent:bs=on:bsr=on:cond=on:er=known:fde=none:nm=4:nwc=1.3:sims=off:sp=frequency:urr=on:stl=62_123");
      quick.push("lrs+1011_1_bd=preordered:flr=on:fsd=off:fsr=off:irw=on:lcm=reverse:msp=off:nm=2:nwc=10.0:sos=on:sp=reverse_weighted_frequency:tgt=full:stl=62_102");
      quick.push("dis+3_3:2_aac=none:fsd=off:fde=none:lcm=reverse:nm=32:nicw=on:sos=on:sac=on:sp=occurrence_102");
      quick.push("dis+1_4:5_av=off:ep=RS:fsd=off:lcm=predicate:nm=2:nwc=1.5:sp=weighted_frequency_102");
      quick.push("lrs-1_4:5_av=off:bd=off:bsr=on:fsd=off:lcm=predicate:nm=4:sos=on:stl=62_98");
      quick.push("dis+1011_4:3_av=off:bd=preordered:drc=off:fsd=off:fde=none:nm=4:nwc=10.0_96");
      quick.push("ott+1002_2:5_acc=on:bd=preordered:bsr=on:er=known:flr=on:fsd=off:fde=none:msp=off:nm=64:sos=on:sac=on:sp=reverse_frequency_71");
      quick.push("ott-1010_1_add=off:afr=on:amm=off:bsr=on:bce=on:er=known:flr=on:fde=none:gsp=on:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.2:nicw=on:sas=z3:sos=on:sac=on:urr=on_58");
      quick.push("dis+2_3:4_av=off:bd=preordered:drc=off:ep=RS:fsd=off:fde=none:gsp=on:lcm=predicate:nm=64:nwc=1.2:sims=off:sp=weighted_frequency_56");
      quick.push("dis+1011_2:3_av=off:cond=on:ep=RS:flr=on:fsd=off:lcm=reverse:nm=0:nwc=2.5:sp=frequency_42");
      quick.push("dis+1011_9:1_ep=RS:fsd=off:fde=unused:nm=4:nwc=4.0:sos=all_35");
      quick.push("lrs+1002_3:4_add=off:ep=RST:fsd=off:fde=none:gs=on:sos=on:sp=scramble:stl=62_33");
      quick.push("lrs-11_32_amm=off:bce=on:cond=on:er=filter:fsd=off:fde=none:gs=on:gsem=on:lcm=reverse:nm=4:nwc=1.1:sos=all:sac=on:sp=frequency:urr=on:stl=125_27");
      quick.push("dis-4_10:1_acc=on:anc=none:flr=on:fsd=off:fde=none:gsp=on:gs=on:gsem=off:lcm=reverse:lma=on:nm=4:nicw=on:sos=all:sp=weighted_frequency:tgt=ground_23");
      quick.push("ott-10_4:3_add=off:bd=off:br=off:fsd=off:fde=none:irw=on:nwc=2.5:sas=z3:sims=off:sos=all:sac=on:sp=scramble:urr=on_21");
      quick.push("dis+4_3:1_bce=on:drc=off:er=filter:flr=on:fsd=off:gsp=on:nm=2:sims=off:sos=all:sac=on:sp=frequency_18");
      quick.push("lrs-1_10:1_drc=off:ep=RS:fsd=off:sos=on:stl=62_10");
      quick.push("lrs-1010_3_aac=none:anc=none:er=known:fsd=off:fde=unused:gs=on:lcm=predicate:sos=on:sp=weighted_frequency:tgt=ground:stl=62_5");
    }
    else if (atoms <= 150000) {
      // total time: 6694
      quick.push("lrs+11_4:3_aac=none:add=off:amm=off:anc=none:bd=preordered:bs=on:bce=on:flr=on:fsd=off:fsr=off:fde=none:nwc=2.5:sims=off:sp=reverse_arity:tgt=full:stl=188_802");
      quick.push("lrs-1010_20_afr=on:anc=all_dependent:bs=on:bsr=on:cond=on:er=known:fde=none:nm=4:nwc=1.3:sims=off:sp=frequency:urr=on:stl=62_619");
      quick.push("dis-1010_1_fsd=off:fsr=off:fde=none:nm=4:sos=all:urr=ec_only_615");
      quick.push("lrs+10_7_av=off:bd=preordered:bs=on:ep=RS:fsd=off:irw=on:nm=4:nwc=1.2:sos=all:tgt=full:urr=ec_only:stl=62_571");
      quick.push("ott+1011_2_afr=on:amm=sco:anc=all:bs=unit_only:bsr=on:cond=on:er=known:fde=unused:gs=on:gsem=on:lcm=reverse:lma=on:msp=off:nm=2:nwc=1.1:nicw=on:sas=z3:sos=all:sac=on:sp=reverse_arity_550");
      quick.push("lrs+1011_1_bd=preordered:flr=on:fsd=off:fsr=off:irw=on:lcm=reverse:msp=off:nm=2:nwc=10.0:sos=on:sp=reverse_weighted_frequency:tgt=full:stl=62_428");
      quick.push("lrs+1002_3:4_add=off:ep=RST:fsd=off:fde=none:gs=on:sos=on:sp=scramble:stl=62_388");
      quick.push("dis+1_2:7_add=off:afr=on:amm=off:bd=off:cond=on:er=known:fsd=off:fde=unused:gsp=on:lcm=predicate:nwc=4.0:nicw=on:sos=on:sac=on:sp=occurrence:tgt=ground_325");
      quick.push("ott+1011_2_aac=none:bsr=on:ep=R:fsd=off:fde=unused:nm=16:nwc=1.5:sas=z3:sos=on_306");
      quick.push("lrs-2_10:1_aac=none:add=off:afr=on:anc=all_dependent:bd=preordered:bs=unit_only:drc=off:fsd=off:fsr=off:gs=on:gsaa=from_current:irw=on:lma=on:msp=off:nm=2:nwc=1.1:nicw=on:sos=all:sp=occurrence:tgt=full:stl=62_260");
      quick.push("dis+1011_4:3_av=off:bd=preordered:drc=off:fsd=off:fde=none:nm=4:nwc=10.0_216");
      quick.push("ott+1_13_aac=none:anc=all_dependent:drc=off:er=known:fsd=off:lcm=reverse:nm=2:nwc=2.5:sos=on:sac=on:tgt=ground_216");
      quick.push("dis+1011_3:2_av=off:ep=RST:fsd=off:fde=none:gsp=on:nm=2:nwc=2.0:sos=on:sp=reverse_frequency_216");
      quick.push("lrs+2_5:4_anc=none:br=off:fde=unused:gsp=on:nm=32:nwc=1.3:sims=off:sos=all:urr=on:stl=62_214");
      quick.push("dis+1011_2:1_add=off:afr=on:er=known:fde=unused:nwc=1.3:nicw=on:sas=z3:sims=off:sos=on:sac=on:tgt=full_188");
      quick.push("ott+1010_2:5_bd=off:fsd=off:fde=none:nm=16:sos=on_174");
      quick.push("lrs+1002_1_aac=none:amm=off:anc=all_dependent:ep=RS:fsd=off:fsr=off:lcm=predicate:nm=16:nwc=1.2:nicw=on:sas=z3:sos=on:stl=62_117");
      quick.push("dis+1011_4_add=large:amm=off:sims=off:sac=on:sp=frequency:tgt=ground_111");
      quick.push("dis+11_8:1_amm=sco:drc=off:ep=R:er=known:flr=on:fde=none:gsp=on:lcm=predicate:lma=on:nwc=1.2:nicw=on:sos=all:sp=weighted_frequency:tgt=full_100");
      quick.push("dis-1010_2:5_av=off:bd=off:fsd=off:fde=none:nm=4:sos=on:sp=occurrence_62");
      quick.push("dis+1011_3_av=off:bd=off:er=known:fsd=off:fde=unused:irw=on:nm=64:nwc=1.3:sos=on:sp=reverse_arity_60");
      quick.push("ott+1002_2:5_acc=on:bd=preordered:bsr=on:er=known:flr=on:fsd=off:fde=none:msp=off:nm=64:sos=on:sac=on:sp=reverse_frequency_50");
      quick.push("lrs-1_10:1_drc=off:ep=RS:fsd=off:sos=on:stl=62_48");
      quick.push("lrs+2_3:4_av=off:bd=preordered:fsd=off:fde=none:lcm=predicate:nm=2:sos=on:sp=reverse_arity:stl=62_42");
      quick.push("lrs-1010_3_aac=none:anc=none:er=known:fsd=off:fde=unused:gs=on:lcm=predicate:sos=on:sp=weighted_frequency:tgt=ground:stl=62_16");
    }
    else {
      // total time: 7883
      quick.push("dis+1011_3_av=off:bd=off:er=known:fsd=off:fde=unused:irw=on:nm=64:nwc=1.3:sos=on:sp=reverse_arity_634");
      quick.push("lrs-1_4:5_av=off:bd=off:bsr=on:fsd=off:lcm=predicate:nm=4:sos=on:stl=62_630");
      quick.push("dis-1003_4_aac=none:bd=off:bs=on:bce=on:er=known:fsd=off:fsr=off:gsp=on:gs=on:irw=on:lcm=reverse:nm=16:nicw=on:sas=z3:sims=off:sos=on:sac=on:sp=reverse_arity:tha=off:thf=on:thi=strong:tgt=ground:uwa=ground_585");
      quick.push("lrs+2_3:4_av=off:bd=preordered:fsd=off:fde=none:lcm=predicate:nm=2:sos=on:sp=reverse_arity:stl=62_548");
      quick.push("ott+1_13_aac=none:anc=all_dependent:drc=off:er=known:fsd=off:lcm=reverse:nm=2:nwc=2.5:sos=on:sac=on:tgt=ground_543");
      quick.push("ott+4_40_av=off:bce=on:fsd=off:fde=unused:nm=4:nwc=1.1:sos=all:sp=frequency_487");
      quick.push("dis+1011_2:1_add=off:afr=on:er=known:fde=unused:nwc=1.3:nicw=on:sas=z3:sims=off:sos=on:sac=on:tgt=full_476");
      quick.push("lrs+10_9:1_amm=off:bd=preordered:bs=unit_only:drc=off:er=known:fsd=off:fde=none:gsp=on:irw=on:lcm=predicate:lma=on:nm=16:nwc=1.1:sims=off:sos=all:sac=on:sp=scramble:tgt=ground:urr=on:stl=188_470");
      quick.push("dis+11_8:1_amm=sco:drc=off:ep=R:er=known:flr=on:fde=none:gsp=on:lcm=predicate:lma=on:nwc=1.2:nicw=on:sos=all:sp=weighted_frequency:tgt=full_457");
      quick.push("lrs+11_20_av=off:bd=off:drc=off:fsd=off:fde=none:lma=on:nm=4:sos=all:stl=62_409");
      quick.push("dis+11_4:5_aac=none:add=off:anc=none:bd=preordered:bs=on:ep=RST:fsd=off:gs=on:gsem=on:lma=on:msp=off:nm=2:nwc=1.3:sas=z3:sos=all:sac=on:sp=weighted_frequency:urr=ec_only_380");
      quick.push("lrs+1010_4:5_fsd=off:fde=unused:nm=4:sos=on:stl=62_363");
      quick.push("ott+1011_2_aac=none:bsr=on:ep=R:fsd=off:fde=unused:nm=16:nwc=1.5:sas=z3:sos=on_256");
      quick.push("lrs+1002_3:4_add=off:ep=RST:fsd=off:fde=none:gs=on:sos=on:sp=scramble:stl=62_249");
      quick.push("dis-4_10:1_acc=on:anc=none:flr=on:fsd=off:fde=none:gsp=on:gs=on:gsem=off:lcm=reverse:lma=on:nm=4:nicw=on:sos=all:sp=weighted_frequency:tgt=ground_247");
      quick.push("ott+1010_2:5_bd=off:fsd=off:fde=none:nm=16:sos=on_226");
      quick.push("lrs-1_10:1_drc=off:ep=RS:fsd=off:sos=on:stl=62_216");
      quick.push("ott+1011_4_er=known:fsd=off:nm=4:tgt=ground_201");
      quick.push("ott+1002_2:5_acc=on:bd=preordered:bsr=on:er=known:flr=on:fsd=off:fde=none:msp=off:nm=64:sos=on:sac=on:sp=reverse_frequency_109");
      quick.push("lrs+1002_1_aac=none:amm=off:anc=all_dependent:ep=RS:fsd=off:fsr=off:lcm=predicate:nm=16:nwc=1.2:nicw=on:sas=z3:sos=on:stl=62_98");
      quick.push("lrs+10_50_aac=none:bsr=on:fsd=off:fde=none:nm=4:sas=z3:sos=on:tgt=full:stl=62_96");
      quick.push("lrs+10_7_av=off:bd=preordered:bs=on:ep=RS:fsd=off:irw=on:nm=4:nwc=1.2:sos=all:tgt=full:urr=ec_only:stl=62_90");
      quick.push("dis+1011_9:1_ep=RS:fsd=off:fde=unused:nm=4:nwc=4.0:sos=all_69");
      quick.push("lrs-1010_3_aac=none:anc=none:er=known:fsd=off:fde=unused:gs=on:lcm=predicate:sos=on:sp=weighted_frequency:tgt=ground:stl=62_44");
    }
    break;    
    
  case Property::HNE:
  case Property::NNE:
  case Property::FNE:
  case Property::EPR:
    // total time: 6976
    quick.push("lrs-1_7_acc=on:amm=off:anc=all:bs=on:bsr=on:cond=fast:flr=on:fsr=off:gsp=on:lcm=reverse:lma=on:msp=off:nm=0:nwc=1.2:sp=frequency:stl=188_1354");
    quick.push("dis-1002_1_av=off:bsr=on:cond=on:flr=on:fsr=off:gsp=on:nwc=2.0:sims=off_1218");
    quick.push("lrs+11_4:3_aac=none:add=off:amm=off:anc=none:bd=preordered:bs=on:bce=on:flr=on:fsd=off:fsr=off:fde=none:nwc=2.5:sims=off:sp=reverse_arity:tgt=full:stl=188_1106");
    quick.push("dis-1_128_add=large:amm=sco:anc=all_dependent:bs=on:bsr=on:bce=on:cond=fast:fsr=off:gsp=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=32:nwc=4.0:nicw=on:sac=on:sp=weighted_frequency_692");
    quick.push("ott-1010_5_add=off:amm=off:anc=none:bce=on:cond=fast:flr=on:lma=on:nm=2:nwc=1.1:sp=occurrence:tgt=ground_470");
    quick.push("ott+10_8_br=off:cond=on:fsr=off:gsp=on:nm=16:nwc=3.0:sims=off:sp=reverse_frequency:urr=on_415");
    quick.push("dis+3_1024_av=off:fsr=off:gsp=on:lcm=predicate:nm=4:sos=all:sp=weighted_frequency_338");
    quick.push("ott+10_8:1_br=off:cond=on:ep=RSTC:fsd=off:nm=0:sos=all:sp=reverse_weighted_frequency:tgt=full:urr=on_336");
    quick.push("dis-1002_12_add=off:bs=on:bsr=on:cond=on:flr=on:gsp=on:gs=on:gsem=off:nm=4:sims=off:tgt=ground_233");
    quick.push("ott+1_128_av=off:bsr=on:fsr=off:lcm=predicate:nm=4:nwc=1.3:sp=weighted_frequency:urr=on_199");
    quick.push("ott+11_2:5_anc=all_dependent:bs=on:bsr=on:drc=off:fsd=off:fsr=off:lcm=reverse:lma=on:nm=4:sos=theory:sp=frequency_195");
    quick.push("dis+1004_1024_amm=off:anc=none:cond=on:gsp=on:lcm=reverse:nm=16:nwc=2.0:sims=off:sos=on:sac=on:tgt=ground_136");
    quick.push("lrs+1010_8_av=off:bs=unit_only:bsr=on:gsp=on:lma=on:nm=2:sims=off:sp=reverse_frequency:urr=ec_only:stl=125_111");
    quick.push("ott-1_1024_av=off:bsr=on:flr=on:fsr=off:lma=on:nm=2:nwc=1.5:sp=weighted_frequency:urr=on_84");
    quick.push("ott-1003_24_aac=none:gsp=on:nm=2:sos=all:urr=on_48");
    quick.push("lrs-10_64_acc=on:add=off:afr=on:flr=on:gs=on:lma=on:nm=4:nwc=4.0:sp=reverse_arity:tgt=ground:stl=62_29");
    quick.push("ott+1011_2_aac=none:bsr=on:ep=R:fsd=off:fde=unused:nm=16:nwc=1.5:sas=z3:sos=on_6");
    quick.push("lrs+1_5:4_fsr=off:gsp=on:nm=4:nwc=2.5:stl=62_6");
    break;

  case Property::UEQ: // slowness 1.3
    if (props != 0) {
      if (atoms <= 16) {
        // total instructions: 1517.4g (~ 505s)
        quick.push("ott+10_3_av=off:bd=preordered:drc=off:fde=none:nwc=5.0:sims=off:sp=reverse_arity:to=lpo:tgt=ground:i=234028_0");
        quick.push("lrs+10_2_av=off:bd=preordered:drc=off:nwc=10.0:sims=off:sil=385500:i=205304_0");
        quick.push("dis+10_2:3_av=off:bd=off:drc=off:nwc=1.1:sims=off:sp=reverse_weighted_frequency:to=lpo:tgt=ground:i=194228_0");
        quick.push("lrs+10_4_av=off:bd=preordered:drc=off:sp=occurrence:tgt=ground:sil=275500:i=172977_0");
        quick.push("lrs+10_28_av=off:drc=off:fde=unused:nwc=1.2:sims=off:sp=frequency:sil=275500:i=171647_0");
        quick.push("ott+10_128_av=off:bd=preordered:drc=off:fde=unused:tgt=ground:i=160378_0");
        quick.push("dis+10_3:4_av=off:fde=unused:sims=off:to=lpo:tgt=ground:i=77404_0");
        quick.push("ott+10_2_av=off:bd=preordered:drc=off:fde=unused:sp=reverse_arity:tgt=ground:i=73842_0");
        quick.push("dis+10_32_av=off:drc=off:sp=occurrence:tgt=ground:i=52169_0");
        quick.push("ott+10_12_av=off:bd=off:drc=off:fde=unused:sims=off:to=lpo:tgt=ground:i=38898_0");
        quick.push("ott+10_15_av=off:bd=preordered:drc=off:sp=weighted_frequency:i=28368_0");
        quick.push("lrs+10_1_av=off:bd=off:fde=none:nwc=5.0:sims=off:sp=occurrence:to=lpo:sil=220500:i=27885_0");
        quick.push("ott+10_14_av=off:drc=off:sims=off:sp=reverse_frequency:tgt=ground:i=27444_0");
        quick.push("dis+10_1024_av=off:ep=RSTC:fde=unused:sims=off:sp=occurrence:to=lpo:tgt=ground:i=24110_0");
        quick.push("lrs+10_10:1_av=off:bd=preordered:drc=off:fde=none:nwc=10.0:sims=off:to=lpo:sil=110500:i=17278_0");
        quick.push("ott+10_4_av=off:drc=off:sims=off:to=lpo:tgt=ground:i=13343_0");
        quick.push("ott+10_1024_av=off:drc=off:fde=unused:nwc=10.0:sp=occurrence:to=lpo:i=3327_0");
        quick.push("dis+10_2_av=off:fde=none:nwc=2.0:i=1719_0");
        quick.push("dis+10_32_av=off:bd=off:drc=off:fde=none:nwc=2.5:sp=reverse_frequency:tgt=ground:i=1348_0");
        quick.push("dis+10_20_av=off:fde=none:nwc=5.0:sims=off:i=1119_0");
        quick.push("dis+10_2:5_av=off:fde=unused:sims=off:tgt=full:i=560_0");
      }
      else {
        // total instructions: 1198.7g (~ 399s)
        quick.push("lrs+10_128_av=off:drc=off:sims=off:tgt=ground:sil=385500:i=265200_0");
        quick.push("lrs+10_2_av=off:drc=off:fde=unused:nwc=1.3:sp=reverse_frequency:sil=385500:i=261780_0");
        quick.push("dis+10_1_av=off:bd=preordered:drc=off:nwc=5.0:sims=off:to=lpo:i=156125_0");
        quick.push("dis+10_3:4_av=off:fde=unused:sims=off:to=lpo:tgt=ground:i=152949_0");
        quick.push("lrs+10_6_av=off:drc=off:fde=unused:sp=reverse_arity:tgt=ground:sil=220500:i=127160_0");
        quick.push("dis+10_128_av=off:drc=off:fde=unused:nwc=1.1:sims=off:sp=reverse_weighted_frequency:tgt=ground:i=84123_0");
        quick.push("ott+10_4_av=off:drc=off:sims=off:to=lpo:tgt=ground:i=70957_0");
        quick.push("ott+10_9_av=off:drc=off:fde=none:nwc=10.0:sims=off:sp=reverse_arity:to=lpo:i=37704_0");
        quick.push("ott+10_10_av=off:bd=preordered:drc=off:fde=none:nwc=2.0:sp=occurrence:i=37659_0");
        quick.push("ott+10_2_av=off:bd=preordered:drc=off:fde=unused:sims=off:sp=reverse_frequency:i=5612_0");
        quick.push("ott+10_20_av=off:drc=off:fde=none:sims=off:sp=reverse_weighted_frequency:tgt=ground:i=4434_0");
      }
    }
    else if (atoms <= 9) {
      // total instructions: 1280.9g (~ 426s)
      quick.push("dis+10_50_av=off:bd=preordered:drc=off:sims=off:sp=reverse_arity:to=lpo:i=317119_0");
      quick.push("lrs+10_4_av=off:bd=preordered:drc=off:sp=occurrence:tgt=ground:sil=275500:i=238848_0");
      quick.push("ott+10_8_av=off:bd=preordered:drc=off:fde=none:sims=off:sp=reverse_frequency:tgt=ground:i=210118_0");
      quick.push("ott+10_128_av=off:bd=preordered:drc=off:fde=unused:tgt=ground:i=180102_0");
      quick.push("lrs+10_3:2_av=off:drc=off:fde=unused:sims=off:to=lpo:sil=165500:i=147361_0");
      quick.push("dis+10_1_av=off:bd=preordered:drc=off:nwc=5.0:sims=off:to=lpo:i=96703_0");
      quick.push("lrs+10_128_av=off:bd=preordered:drc=off:fde=none:to=lpo:tgt=ground:sil=110500:i=64108_0");
      quick.push("ott+10_2_av=off:bd=preordered:drc=off:fde=unused:sp=reverse_arity:tgt=ground:i=18218_0");
      quick.push("ott+10_2_av=off:bd=preordered:drc=off:fde=unused:sims=off:sp=reverse_frequency:i=12310_0");
    }
    else if (atoms <= 10) {
      // total instructions: 1798.3g (~ 599s)
      quick.push("dis+10_32_av=off:bd=preordered:drc=off:fde=unused:sims=off:sp=reverse_frequency:to=lpo:tgt=ground:i=302714_0");
      quick.push("ott+10_8:1_av=off:bd=preordered:drc=off:sp=reverse_frequency:i=265881_0");
      quick.push("ott+10_16_av=off:bd=preordered:drc=off:fde=none:sims=off:sp=reverse_weighted_frequency:tgt=ground:i=228083_0");
      quick.push("ott+10_8_av=off:bd=preordered:drc=off:fde=none:sims=off:sp=reverse_frequency:tgt=ground:i=219517_0");
      quick.push("lrs+10_20_av=off:bd=off:drc=off:fde=none:sims=off:sp=reverse_weighted_frequency:tgt=ground:sil=275500:i=165359_0");
      quick.push("ott+10_2_av=off:bd=preordered:drc=off:fde=unused:sims=off:sp=reverse_frequency:i=145876_0");
      quick.push("ott+10_4_av=off:bd=off:drc=off:fde=none:sims=off:tgt=ground:i=145392_0");
      quick.push("lrs+10_10_av=off:drc=off:fde=none:sims=off:sp=reverse_frequency:tgt=ground:sil=275500:i=129472_0");
      quick.push("lrs+10_8:1_av=off:bd=preordered:drc=off:sims=off:sil=275500:i=91225_0");
      quick.push("lrs+10_10_av=off:drc=off:fde=unused:nwc=1.7:sp=reverse_weighted_frequency:sil=385500:i=78251_0");
      quick.push("ott+10_2_av=off:bd=off:drc=off:tgt=ground:i=29962_0");
      quick.push("ott+10_50_av=off:bd=off:drc=off:sp=reverse_weighted_frequency:tgt=ground:i=2086_0");
    }
    else {
      // total instructions: 1602.6g (~ 534s)
      quick.push("lrs+10_28_av=off:bd=preordered:drc=off:nwc=1.5:sims=off:sp=reverse_weighted_frequency:tgt=ground:sil=385500:i=291678_0");
      quick.push("ott+10_12_av=off:bd=off:drc=off:fde=unused:sims=off:to=lpo:tgt=ground:i=249497_0");
      quick.push("ott+10_2:3_av=off:bd=off:drc=off:fde=none:sp=reverse_weighted_frequency:to=lpo:tgt=ground:i=216654_0");
      quick.push("ott+10_11_av=off:bd=preordered:drc=off:nwc=1.3:sims=off:tgt=ground:i=185331_0");
      quick.push("lrs+10_10_av=off:drc=off:fde=unused:nwc=1.7:sp=reverse_weighted_frequency:sil=385500:i=154575_0");
      quick.push("dis+10_128_av=off:drc=off:fde=unused:nwc=1.1:sims=off:sp=reverse_weighted_frequency:tgt=ground:i=118086_0");
      quick.push("dis+10_6_av=off:bd=preordered:drc=off:fde=none:sims=off:sp=reverse_weighted_frequency:to=lpo:tgt=ground:i=111784_0");
      quick.push("ott+10_4_av=off:drc=off:sims=off:to=lpo:tgt=ground:i=105289_0");
      quick.push("dis+10_32_av=off:bd=off:drc=off:fde=none:nwc=2.5:sp=reverse_frequency:tgt=ground:i=85866_0");
      quick.push("dis+10_8:1_av=off:bd=off:drc=off:nwc=5.0:sims=off:to=lpo:i=21835_0");
      quick.push("lrs+10_3_av=off:fde=none:nwc=1.3:sims=off:sp=occurrence:to=lpo:sil=55500:i=18400_0");
      quick.push("dis+10_1_av=off:bd=preordered:drc=off:nwc=5.0:sims=off:to=lpo:i=17691_0");
      quick.push("ott+10_50_av=off:bd=off:drc=off:sp=reverse_weighted_frequency:tgt=ground:i=17616_0");
      quick.push("dis+10_64_av=off:bd=preordered:drc=off:fde=unused:sims=off:to=lpo:tgt=ground:i=10843_0");
      quick.push("ott+10_20_av=off:drc=off:fde=none:sims=off:sp=reverse_weighted_frequency:tgt=ground:i=4031_0");
      quick.push("ott+10_3:4_av=off:bd=off:drc=off:fde=unused:nwc=2.5:sims=off:sp=weighted_frequency:to=lpo:i=965_0");
    }
    break;
  }
} // getCasc2023Schedule

void Schedules::getCasc2024Schedule(const Property& property, Schedule& quick, Schedule& fallback)
{
  unsigned atoms = property.atoms();
  Property::Category cat = property.category();
  unsigned long props = property.props();

  if (property.hasNumerals() || property.hasInterpretedOperations()) {
    // The TFA division: Typed (monomorphic) First-order with Arithmetic theorems (axioms with a provable conjecture).

    getSnakeTptpUnsSchedule(property,quick);

  } else if (cat == Property::Category::UEQ) {
    // The UEQ division: Unit EQuality clause normal form theo rems (unsatisfiable clause sets)

    auto [propZsmall10,propZbig10,propNZsmall14,propNZbig14] = (props == 0) ?
        (atoms <= 10 ? std::tie(quick,fallback,fallback,fallback) : std::tie(fallback,quick,fallback,fallback)) :
        (atoms <= 14 ? std::tie(fallback,fallback,quick,fallback) : std::tie(fallback,fallback,fallback,quick));

    propZsmall10.push("ott+10_4:13_drc=encompass:sil=256000:bsd=on:sp=reverse_frequency:urr=on:i=125345:rawr=on_0");
    propZsmall10.push("lrs+10_25:89_sil=256000:tgt=ground:lwlo=on:s2a=on:i=224446:s2at=5.0:fsr=off:awrs=converge:awrsf=90_0");

    propZsmall10.push("lrs+10_1:1_to=lpo:drc=encompass:sil=2000:fde=unused:sp=const_min:i=107:bs=unit_only:bd=preordered:ins=1:rawr=on:crc=on:sfv=off:plsq=on:plsql=on:plsqc=1_0");
    propZsmall10.push("lrs+10_1:32_drc=encompass:sil=256000:i=140:crc=on_0");
    propZsmall10.push("lrs+10_85441:1048576_drc=encompass:sil=64000:i=401:awrs=converge:sp=reverse_frequency:dpc=on:bd=preordered:fsr=off:ss=included:st=3.0:fde=none_0");
    propZsmall10.push("dis+10_1:128_drc=encompass:sil=256000:sp=occurrence:i=1122:kws=precedence:fsr=off_0");
    propZsmall10.push("dis+10_1:24_drc=encompass:sil=256000:tgt=ground:spb=goal:i=313:bd=preordered:crc=on:croc=on_0");
    propZsmall10.push("dis+10_1:9_bsr=unit_only:slsqr=31,32:sil=256000:tgt=full:urr=on:slsqc=2:slsq=on:i=1149:s2at=5.0:slsql=off:ins=1:rawr=on:fd=preordered:drc=encompass_0");
    propZsmall10.push("lrs+10_1:10_drc=encompass:sil=2000:tgt=ground:plsq=on:plsqr=92626939,1048576:sp=occurrence:fd=preordered:i=1914:kws=precedence:ins=8:rawr=on_0");
    propZsmall10.push("lrs+10_16:1_bsr=on:drc=encompass:sil=64000:i=281:bd=off:to=lpo_0");
    propZsmall10.push("lrs+10_1:64_drc=encompass:sil=2000:fde=none:sp=reverse_arity:s2a=on:i=1826:ins=2:dpc=on:awrs=decay:awrsf=200_0");
    propZsmall10.push("dis+10_1:1024_slsqr=7,2:to=lpo:sil=256000:tgt=full:s2agt=8:slsqc=1:slsq=on:s2a=on:i=807:rawr=on_0");
    propZsmall10.push("dis+10_1:14_bsr=unit_only:to=lpo:drc=encompass:sil=256000:tgt=ground:urr=on:slsq=on:i=519:awrs=converge:awrsf=50:rawr=on:fsr=off_0");
    propZsmall10.push("lrs+10_1:1_to=lpo:drc=encompass:sil=8000:tgt=full:sp=const_frequency:i=525:lwlo=on:nwc=10.0_0");
    propZsmall10.push("lrs+10_1:32_drc=encompass:sil=256000:tgt=ground:sp=reverse_frequency:s2a=on:i=4287:s2at=5.0:kws=precedence_0");
    propZsmall10.push("lrs+10_1:1024_sil=2000:tgt=ground:plsq=on:sp=frequency:s2a=on:i=1997:kws=precedence:rawr=on:bd=off:awrs=converge:awrsf=10:ins=2_0");
    propZsmall10.push("dis+10_1:3_to=lpo:drc=encompass:sil=256000:tgt=ground:i=637:fsr=off_0");
    propZsmall10.push("lrs+10_1:512_sil=4000:tgt=ground:sp=reverse_frequency:s2a=on:i=702:bs=unit_only:bd=off:ss=axioms:rawr=on:slsq=on:slsqc=3:slsqr=19,8_0");
    propZsmall10.push("lrs+10_1:4_drc=encompass:sil=16000:lwlo=on:st=-1.0:i=6272:ss=axioms_0");
    propZsmall10.push("lrs+10_1:10_drc=encompass:sil=16000:tgt=ground:plsq=on:fd=preordered:i=10171:bd=preordered:ins=1:rawr=on:ss=axioms:sgt=16_0");
    propZsmall10.push("lrs+10_7:24_to=lpo:drc=encompass:sil=128000:fde=unused:sp=const_min:spb=goal:i=1061:crc=on:slsq=on:fdi=256:nwc=10.0:dpc=on:ss=included:st=2.0_0");
    propZsmall10.push("lrs+10_1:14_slsqr=3,4:drc=encompass:sil=4000:tgt=ground:sp=const_max:s2agt=16:slsqc=3:slsq=on:i=1157:kws=precedence:slsql=off:crc=on:rawr=on_0");
    propZsmall10.push("lrs+10_25:999_drc=encompass:sil=256000:tgt=full:spb=intro:i=1382:kws=precedence:awrs=converge:awrsf=53:crc=on:croc=on:bd=off:bs=unit_only_0");
    propZsmall10.push("ott+10_21691:1048576_drc=encompass:sil=256000:tgt=ground:sims=off:sp=occurrence:spb=goal_then_units:fd=preordered:i=2271:kws=precedence:av=off:fsr=off:uhcvi=on:fsd=on:fsdmm=2:slsq=on:slsql=off:slsqc=1:slsqr=320859,1048576:s2at=3.0:crc=on:rawr=on:ss=axioms:sd=2_0");
    propZsmall10.push("lrs+10_1:128_drc=encompass:sil=256000:tgt=full:sp=unary_frequency:spb=non_intro:i=2392:kws=precedence:crc=on:croc=on_0");
    propZsmall10.push("ott+10_1:128_drc=encompass:sil=256000:plsq=on:s2a=on:i=2544:kws=precedence:dpc=on:bd=preordered:ss=axioms_0");
    propZsmall10.push("lrs+10_1:40_drc=encompass:sil=256000:tgt=full:sp=unary_frequency:spb=goal_then_units:i=5255:kws=frequency:rawr=on:crc=on:croc=on:fd=preordered_0");
    propZsmall10.push("ott+10_2:5_bsr=unit_only:to=lpo:drc=encompass:sil=256000:sp=reverse_frequency:i=2866:ins=1:dpc=on:rawr=on_0");
    propZsmall10.push("dis+10_1:1024_slsqr=5,2:sil=256000:tgt=ground:urr=on:slsqc=2:slsq=on:i=3253:ins=1:crc=on:rawr=on_0");
    propZsmall10.push("lrs+10_1:1024_slsqr=1,4:drc=encompass:sil=256000:tgt=full:sp=reverse_frequency:slsqc=4:slsq=on:s2a=on:i=7906:bd=off:crc=on:croc=on:ss=axioms:rawr=on:st=3.0:awrs=converge:foolp=on_0");
    propZsmall10.push("ott+10_1:10_drc=encompass:sil=256000:sp=reverse_frequency:fd=preordered:i=4168:ins=2:bd=off:ss=axioms_0");
    propZsmall10.push("lrs+10_1:6_drc=encompass:sil=32000:tgt=ground:s2agt=8:s2a=on:i=8705_0");
    propZsmall10.push("dis+10_1:16_sil=256000:i=5821:bs=unit_only:rawr=on:plsq=on:to=lpo_0");
    propZsmall10.push("dis+10_8125:131072_drc=encompass:sil=256000:tgt=full:sp=occurrence:lma=on:fd=preordered:i=14311:kws=precedence:doe=on:awrs=decay:awrsf=50:dpc=on:uhcvi=on:ss=axioms:crc=on_0");
    propZsmall10.push("ott+10_1:1_drc=encompass:sil=256000:plsq=on:fd=preordered:st=5.0:s2a=on:i=35818:ins=1:ss=axioms:rawr=on_0");
    propZsmall10.push("lrs+10_1:1_drc=encompass:sil=16000:fd=preordered:i=9154:bs=on:crc=on_0");
    propZsmall10.push("lrs+10_1:16_drc=encompass:sil=16000:tgt=full:lwlo=on:s2pl=no:i=10003:av=off:rawr=on_0");
    propZsmall10.push("ott+10_10:3_sil=256000:fde=unused:sp=frequency:spb=goal:i=11196:bs=on:kws=precedence:ins=1:dpc=on:rawr=on:nwc=3.0:drc=encompass_0");
    propZsmall10.push("lrs+10_1:1_drc=encompass:sil=256000:tgt=ground:sp=unary_first:sos=on:i=36276:kws=precedence:lwlo=on:crc=on_0");
    propZsmall10.push("lrs+10_13:1_bsr=on:drc=encompass:sil=64000:fd=preordered:i=12509:bd=off:crc=on_0");
    propZsmall10.push("lrs+10_3:14_drc=encompass:sil=128000:sp=const_frequency:spb=goal:lwlo=on:i=27445:kws=precedence:crc=on:nwc=5.0:awrs=decay:awrsf=255:s2pl=no:s2agt=32:fsd=on:fsr=off:lma=on_0");
    propZsmall10.push("lrs+10_1:1024_sil=256000:lwlo=on:i=31665:kws=precedence:awrs=converge:awrsf=240:drc=encompass:fd=preordered:tgt=ground_0");
    propZsmall10.push("dis+10_1:256_to=lpo:drc=encompass:sil=256000:spb=goal:fd=preordered:i=18386:crc=on:croc=on:bs=unit_only_0");
    propZsmall10.push("dis+10_1:20_drc=encompass:sil=256000:tgt=full:sp=reverse_frequency:spb=intro:fd=preordered:i=22321:kws=precedence:crc=on:croc=on:ins=1_0");
    propZsmall10.push("dis+10_1:166_drc=encompass:sil=256000:tgt=full:i=26531:fsr=off:spb=non_intro:dpc=on:to=lpo:rawr=on_0");
    propZsmall10.push("ott+10_1:4_drc=encompass:sil=256000:st=3.0:i=32454:ss=axioms:dpc=on:bd=preordered:slsq=on:slsqc=1:slsqr=1,2_0");
    propZsmall10.push("lrs+10_3:58_drc=encompass:sil=256000:tgt=full:bsd=on:sp=reverse_arity:lwlo=on:s2a=on:i=157761:s2at=2.0:kws=precedence:bsr=on:irw=on:dpc=on:doe=on:bs=on:br=off:erd=off:s2agt=20:nwc=8.95214440448525:cond=fast:foolp=on:spb=non_intro:sfv=off:crc=on:fde=unused:ins=3_0");
    propZsmall10.push("lrs+10_1:6_drc=encompass:sil=256000:tgt=full:spb=non_intro:i=82574:ins=2:crc=on:croc=on:ss=included:bd=preordered_0");

    propZsmall10.push("lrs+10_1:16_drc=encompass:sil=256000:tgt=full:spb=intro:i=58527:kws=precedence:awrs=converge:awrsf=200:ss=axioms:crc=on:croc=on:st=3.0:sp=unary_first_0");
    propZsmall10.push("lrs+10_1:12_drc=encompass:sil=256000:tgt=full:spb=intro:i=72339:kws=precedence:awrs=converge:awrsf=500:crc=on_0");
    propZsmall10.push("ott+10_11413117:1048576_drc=encompass:sil=256000:tgt=ground:fde=unused:plsqc=2:plsq=on:plsqr=1149513,1048576:sp=occurrence:nwc=9.10417:i=125323:kws=precedence:doe=on:awrs=converge:awrsf=286:bd=off:dpc=on:crc=on:croc=on:uhcvi=on:rawr=on:ss=included:st=2.0_0");
    propZsmall10.push("lrs+10_54503:1048576_drc=encompass:sil=256000:tgt=ground:bsd=on:sp=reverse_frequency:lwlo=on:st=3.5:s2a=on:i=174981:s2at=5.5:kws=precedence:ss=included:sgt=50:bsr=unit_only:irw=on:dpc=on:uhcvi=on:doe=on:bs=on:br=off:erd=off_0");
    // total_instr 1391316
    // len(covered) 365


    propZbig10.push("lrs+10_1:12_drc=encompass:sil=256000:tgt=full:spb=intro:i=116130:kws=precedence:awrs=converge:awrsf=500:crc=on_0");
    propZbig10.push("dis+10_5:2_drc=encompass:sil=256000:tgt=ground:sp=reverse_frequency:sos=all:i=207332:bd=off:fsr=off:dpc=on_0");

    propZbig10.push("lrs+10_1:64_drc=encompass:sil=2000:i=105:plsq=on:ss=axioms_0");
    propZbig10.push("lrs+10_3:4_to=lpo:drc=encompass:sil=4000:sp=reverse_frequency:i=126:ss=axioms:sgt=16:s2a=on:s2at=3.0:crc=on:bd=off_0");
    propZbig10.push("ott+10_2:5_bsr=unit_only:to=lpo:drc=encompass:sil=256000:sp=reverse_frequency:i=150:ins=1:dpc=on:rawr=on_0");
    propZbig10.push("lrs+10_1:8_drc=encompass:sil=16000:tgt=ground:i=123:bd=preordered:ss=axioms_0");
    propZbig10.push("lrs+10_1:1_drc=encompass:sil=4000:i=209:ss=axioms:sgt=8:sp=occurrence_0");
    propZbig10.push("lrs+10_1:4_drc=encompass:sil=16000:tgt=ground:lwlo=on:s2a=on:i=192:s2at=2.0_0");
    propZbig10.push("lrs+10_1:7_drc=encompass:sil=64000:tgt=full:spb=non_intro:i=454:awrs=converge:awrsf=67:sp=reverse_frequency:nwc=1.5_0");
    propZbig10.push("lrs+10_1:2_sil=2000:tgt=ground:spb=goal:i=359:kws=precedence:crc=on:croc=on_0");
    propZbig10.push("lrs+10_1:1_sil=4000:sp=occurrence:i=163:ss=axioms:st=3.0:sd=2_0");
    propZbig10.push("lrs+10_1:1024_drc=encompass:sil=4000:tgt=full:i=1030:kws=inv_frequency:awrs=converge_0");
    propZbig10.push("lrs+10_3:1_sil=4000:tgt=ground:i=631:kws=frequency:bd=off:drc=encompass:crc=on_0");
    propZbig10.push("lrs+10_1:3_to=lpo:drc=encompass:sil=4000:tgt=full:i=901:rawr=on:ins=4:bd=off:fd=preordered_0");
    propZbig10.push("lrs+10_1:24_drc=encompass:sil=256000:tgt=full:sp=unary_frequency:spb=non_intro:i=312:ins=2:fsr=off:kws=precedence:crc=on:croc=on:bsr=unit_only:br=off:ss=included:sgt=16:bd=preordered_0");
    propZbig10.push("lrs+10_1:1_drc=encompass:sil=2000:slsq=on:s2a=on:i=1363:s2at=7.0_0");
    propZbig10.push("ott+10_8:1_drc=encompass:sil=256000:i=471:rawr=on:crc=on_0");
    propZbig10.push("lrs+10_1:4_drc=encompass:sil=4000:tgt=full:sp=reverse_arity:st=-1.0:i=2897:kws=precedence:ss=included:lwlo=on:rawr=on:bd=off:urr=on:bsd=on_0");
    propZbig10.push("lrs+10_1:12_sil=2000:tgt=full:sp=reverse_frequency:i=569:kws=inv_frequency:bd=off:fsr=off:rawr=on:awrs=converge_0");
    propZbig10.push("lrs+10_1:1_drc=encompass:sil=2000:st=5.0:s2a=on:i=577:s2at=5.0:sd=1:bd=preordered:crc=on:ss=axioms:sgt=10_0");
    propZbig10.push("lrs+10_8:1_drc=encompass:sil=4000:tgt=ground:spb=non_intro:i=843:bd=off:crc=on_0");
    propZbig10.push("lrs+10_1:1_drc=encompass:sil=2000:tgt=ground:st=5.0:i=1015:bd=off:ss=axioms_0");
    propZbig10.push("lrs+10_15:26_drc=encompass:sil=16000:i=4402:ins=4:crc=on_0");
    propZbig10.push("lrs+10_16:1_to=lpo:sil=32000:urr=ec_only:fd=preordered:nwc=10.0:i=1315:bd=off:crc=on:drc=encompass_0");
    propZbig10.push("lrs+10_8:1_drc=encompass:sil=256000:st=3.0:s2a=on:i=2957:s2at=1.2:ss=axioms:sd=15_0");
    propZbig10.push("lrs+10_3:1_drc=encompass:sil=4000:tgt=full:sp=unary_first:sos=all:lwlo=on:i=3869:crc=on_0");
    propZbig10.push("lrs+10_1:1_drc=encompass:sil=256000:tgt=ground:s2agt=8:s2a=on:i=2041_0");
    propZbig10.push("ott+10_1:28_sil=256000:tgt=full:fd=preordered:i=6716:bd=off_0");
    propZbig10.push("ott+10_1:14_bsr=unit_only:sil=256000:i=2510:sp=weighted_frequency:crc=on_0");
    propZbig10.push("lrs+10_1:10_drc=encompass:sil=16000:tgt=ground:plsq=on:fd=preordered:i=3229:bd=preordered:ins=1:rawr=on:ss=axioms:sgt=16_0");
    propZbig10.push("lrs+10_1:16_drc=encompass:sil=16000:sp=unary_frequency:i=7440:kws=precedence_0");
    propZbig10.push("ott+10_1:64_sil=256000:tgt=full:i=10214:sp=reverse_frequency:bd=off:drc=encompass_0");
    propZbig10.push("lrs+10_3:14_drc=encompass:sil=128000:sp=const_frequency:spb=goal:lwlo=on:i=29852:kws=precedence:crc=on:ins=4_0");
    propZbig10.push("lrs+10_1:6_drc=encompass:sil=32000:tgt=ground:s2agt=8:s2a=on:i=24503_0");
    propZbig10.push("dis+10_1:4_to=lpo:sil=256000:tgt=full:sp=reverse_frequency:spb=goal:i=11902:awrs=converge:awrsf=500:fd=preordered:crc=on:bd=off_0");
    propZbig10.push("dis+10_1:4_drc=encompass:sil=256000:tgt=ground:sos=all:i=13038:kws=inv_arity_squared:fsr=off:dpc=on_0");
    propZbig10.push("lrs+10_1:16_drc=encompass:sil=32000:sp=reverse_frequency:spb=goal:i=28291:kws=inv_arity_squared_0");
    propZbig10.push("dis+10_1:166_drc=encompass:sil=256000:tgt=full:i=19584:fsr=off:spb=non_intro:kws=inv_frequency_0");
    propZbig10.push("lrs+10_1:34_drc=encompass:sil=64000:tgt=ground:lwlo=on:i=37491:kws=frequency:crc=on:croc=on_0");
    propZbig10.push("dis+10_1:64_sil=256000:tgt=full:sp=const_frequency:sos=on:i=57866:bs=on_0");
    propZbig10.push("lrs+10_1:1024_drc=encompass:sil=128000:tgt=ground:sp=frequency:i=58321:kws=precedence_0");
    propZbig10.push("dis+10_1:166_drc=encompass:sil=256000:tgt=full:i=78078:fsr=off:spb=non_intro:dpc=on:to=lpo:rawr=on_0");
    propZbig10.push("ott+10_1:128_bsr=on:drc=encompass:sil=128000:sp=frequency:i=98995:bd=preordered:dpc=on:rawr=on_0");

    // total_instr 838566
    // len(covered) 226

    propNZsmall14.push("ott+10_1:36_drc=encompass:sil=256000:tgt=full:fde=none:st=5.0:i=276418:ss=axioms:sgt=16:sp=occurrence:plsq=on_0");
    propNZsmall14.push("dis+10_1:28_drc=encompass:sil=256000:tgt=ground:i=146946:dpc=on:bs=on_0");

    propNZsmall14.push("dis+10_1:64_sil=256000:i=105:bd=off:fd=off_0");
    propNZsmall14.push("lrs+10_1:1024_drc=encompass:sil=2000:i=149_0");
    propNZsmall14.push("lrs+10_1:1_sil=2000:sos=on:urr=on:st=5.0:i=149:ep=RSTC:ss=axioms:flr=on:fsr=off:br=off_0");
    propNZsmall14.push("lrs+10_1:1024_sil=64000:i=305:to=lpo:drc=encompass:bd=off_0");
    propNZsmall14.push("lrs+10_1:32_slsqr=1,2:drc=encompass:sil=2000:slsqc=1:slsq=on:i=729:slsql=off:fd=preordered:lwlo=on_0");
    propNZsmall14.push("lrs+10_1:7_drc=encompass:sil=64000:i=132:awrs=converge:sp=reverse_frequency:dpc=on:bd=preordered_0");
    propNZsmall14.push("lrs+10_1:7_drc=encompass:sil=64000:tgt=full:spb=non_intro:i=134:awrs=converge:awrsf=67:sp=reverse_frequency:nwc=1.5_0");
    propNZsmall14.push("lrs+10_16:7_drc=encompass:sil=128000:sp=weighted_frequency:lwlo=on:i=118:bs=on:to=lpo:tgt=full:bd=off_0");
    propNZsmall14.push("dis+10_1:1_sil=256000:nwc=10.0:s2agt=32:s2a=on:i=156:fde=none:fd=off_0");
    propNZsmall14.push("lrs+10_1:1024_sil=2000:slsqc=1:slsq=on:i=167:rawr=on:bd=off_0");
    propNZsmall14.push("lrs+10_1:64_sil=32000:tgt=ground:spb=goal_then_units:urr=on:i=687:awrs=converge:awrsf=130:rawr=on:plsq=on:sp=const_frequency:bd=off:drc=encompass:crc=on:kws=precedence_0");
    propNZsmall14.push("dis+10_5:1_to=lpo:sil=256000:tgt=ground:spb=intro:i=187:bd=off:crc=on:rawr=on:fd=preordered:drc=encompass_0");
    propNZsmall14.push("lrs+10_2:1_to=lpo:drc=encompass:sil=8000:tgt=full:sp=const_frequency:i=189:lwlo=on:nwc=10.0:rawr=on_0");
    propNZsmall14.push("dis+10_1:50_sil=256000:nwc=4.1:i=315:bd=off:crc=on:croc=on:fd=off_0");
    propNZsmall14.push("ott+10_2:5_bsr=unit_only:to=lpo:drc=encompass:sil=256000:sp=reverse_frequency:i=323:ins=1:dpc=on:rawr=on_0");
    propNZsmall14.push("lrs+10_1:16_drc=encompass:sil=32000:sp=reverse_frequency:spb=goal:i=252:kws=inv_arity_squared_0");
    propNZsmall14.push("lrs+10_1:8_sil=2000:nwc=3.0:i=263:bd=off:fsr=off:rawr=on:sp=occurrence:fd=off:kws=inv_precedence_0");
    propNZsmall14.push("ott+10_1:28_sil=256000:tgt=full:fd=preordered:i=1545:bd=off_0");
    propNZsmall14.push("lrs+10_1:1_drc=encompass:sil=2000:st=5.0:s2a=on:i=303:s2at=5.0:sd=1:bd=preordered:crc=on:ss=axioms:sgt=10_0");
    propNZsmall14.push("ott+10_1:4_drc=encompass:sil=256000:st=3.0:i=1804:ss=axioms:dpc=on:bd=preordered:slsq=on:slsqc=1:slsqr=1,2_0");
    propNZsmall14.push("dis+10_1:12_slsqr=20,127:sil=256000:fd=off:slsqc=1:slsq=on:i=390:rawr=on:bsr=on_0");
    propNZsmall14.push("dis+10_1:16_slsqr=167,244:drc=encompass:sil=256000:slsqc=1:slsq=on:i=480:kws=inv_arity:awrs=converge:slsql=off:awrsf=61:bd=off:ins=2:rawr=on_0");
    propNZsmall14.push("dis+10_1:2_to=lpo:sil=256000:i=1649:crc=on:croc=on:fd=preordered_0");
    propNZsmall14.push("dis+10_4:1_to=lpo:sil=256000:tgt=ground:spb=goal:fd=preordered:i=525:crc=on_0");
    propNZsmall14.push("lrs+10_8:1_drc=encompass:sil=256000:st=3.0:s2a=on:i=585:s2at=1.2:ss=axioms:sd=15_0");
    propNZsmall14.push("lrs+10_16:1_bsr=on:drc=encompass:sil=64000:i=715:bd=off:to=lpo_0");
    propNZsmall14.push("lrs+10_1:1_slsqr=455249,524288:drc=encompass:sil=2000:tgt=ground:bsd=on:plsq=on:plsqr=32,1:urr=ec_only:slsqc=1:slsq=on:s2a=on:i=770:kws=precedence:slsql=off:rawr=on_0");
    propNZsmall14.push("dis+10_4:27_drc=encompass:sil=256000:tgt=ground:plsq=on:sp=weighted_frequency:s2a=on:i=802:kws=precedence:bd=off:ins=4:rawr=on:fd=preordered:s2agt=8_0");
    propNZsmall14.push("lrs+10_2:1_to=lpo:drc=encompass:sil=4000:tgt=full:sp=const_min:urr=on:nwc=5.0:i=839:rawr=on_0");
    propNZsmall14.push("dis+10_1:16_to=lpo:drc=encompass:sil=256000:tgt=ground:plsq=on:plsqr=1,32:sp=unary_frequency:s2a=on:i=939:awrs=converge:awrsf=340:rawr=on:s2at=2.0_0");
    propNZsmall14.push("lrs+10_1:1024_sil=2000:tgt=ground:plsq=on:sp=frequency:s2a=on:i=1017:kws=precedence:rawr=on:bd=off:awrs=converge:awrsf=10:ins=2_0");
    propNZsmall14.push("dis+10_1:14_bsr=unit_only:to=lpo:drc=encompass:sil=256000:tgt=ground:urr=on:slsq=on:i=1831:awrs=converge:awrsf=50:rawr=on:fsr=off_0");
    propNZsmall14.push("lrs+10_1:1_drc=encompass:sil=32000:tgt=ground:sp=unary_frequency:lwlo=on:i=22426:crc=on:croc=on:kws=precedence_0");
    propNZsmall14.push("ott+10_1:6_drc=encompass:sil=256000:tgt=ground:fde=none:plsq=on:sp=weighted_frequency:s2a=on:i=2595:s2at=2.0:kws=precedence:bd=off:ins=4:dpc=on:ss=axioms:sgt=16:rawr=on_0");
    propNZsmall14.push("ott+10_1:128_slsqr=1,2:drc=encompass:sil=256000:fde=unused:sp=frequency:slsq=on:i=2907:slsql=off_0");
    propNZsmall14.push("dis+10_35:501_sil=256000:tgt=ground:sp=const_max:i=28204:kws=precedence:awrs=decay:awrsf=300_0");
    propNZsmall14.push("lrs+10_1:128_drc=encompass:sil=16000:sp=const_frequency:i=11308:kws=precedence:slsq=on_0");
    propNZsmall14.push("dis+10_1:12_sil=256000:tgt=ground:fde=unused:i=6021:s2a=on:s2agt=8_0");
    propNZsmall14.push("lrs+10_16:1_to=lpo:sil=32000:urr=ec_only:fd=preordered:nwc=10.0:i=15430:bd=off:crc=on:drc=encompass_0");
    propNZsmall14.push("ott+10_2:9_drc=encompass:sil=128000:tgt=full:sp=frequency:nwc=5.0:st=3.0:i=57775:kws=precedence:bd=preordered:dpc=on:ss=axioms:rawr=on:rnwc=on_0");
    propNZsmall14.push("dis+10_1:128_drc=encompass:sil=256000:nwc=6.0:i=21529:fsr=off_0");
    propNZsmall14.push("dis+10_1:1_drc=encompass:sil=256000:tgt=full:i=76551:to=lpo:fde=unused_0");
    propNZsmall14.push("dis+10_1:54_sil=256000:tgt=ground:plsq=on:plsqr=9145955,131072:sp=frequency:spb=goal_then_units:plsql=on:i=50725:doe=on:ins=3:rawr=on:slsq=on:slsqr=1,4:s2at=2.0:slsqc=1_0");
    propNZsmall14.push("lrs+10_1:28_drc=encompass:sil=256000:tgt=full:spb=intro:i=81856:kws=precedence:awrs=converge:awrsf=240:ss=axioms:rawr=on:crc=on:st=3.0:sp=const_frequency_0");
    propNZsmall14.push("lrs+10_1:4_to=lpo:sil=256000:tgt=ground:sp=reverse_arity:spb=goal_then_units:i=106211:fdi=10:bs=unit_only:s2a=on_0");

    // total_instr 925456
    // len(covered) 301

    propNZbig14.push("dis+10_28091:1048576_to=lpo:drc=encompass:sil=128000:tgt=full:erd=off:cond=on:i=107869:doe=on:ins=2:av=off:dpc=on:crc=on:croc=on:s2pl=on:s2agt=5:s2at=4.0:foolp=on_0");
    propNZbig14.push("lrs+10_1:1_drc=encompass:sil=256000:tgt=ground:sp=unary_first:sos=on:i=220312:kws=precedence:lwlo=on:crc=on_0");

    propNZbig14.push("lrs+10_16:1_sfv=off:sil=2000:sp=reverse_frequency:urr=ec_only:br=off:i=126:doe=on:crc=on:to=lpo:fd=preordered:bd=preordered:fsd=on:drc=encompass_0");
    propNZbig14.push("lrs+10_3:107_sil=64000:i=143:ss=axioms:sgt=16:rawr=on:to=lpo:drc=encompass_0");
    propNZbig14.push("lrs+10_2:1_to=lpo:drc=encompass:sil=4000:tgt=full:sp=const_min:urr=on:nwc=5.0:i=129:rawr=on_0");
    propNZbig14.push("lrs+10_1:12_drc=encompass:sil=256000:tgt=full:spb=intro:i=735:kws=precedence:awrs=converge:awrsf=500:crc=on_0");
    propNZbig14.push("dis+10_577:524288_drc=encompass:sil=256000:sp=const_frequency:spb=units:i=214:doe=on:bd=off:av=off:dpc=on:crc=on:croc=on:uhcvi=on:ss=included:rawr=on:to=lpo:slsq=on:slsqr=8,31:s2agt=5:s2at=4.0:fdi=2_0");
    propNZbig14.push("lrs+10_1:64_sil=8000:tgt=full:spb=non_intro:i=204:kws=precedence:plsq=on:awrs=converge:awrsf=30:sp=weighted_frequency:drc=encompass:crc=on:croc=on_0");
    propNZbig14.push("lrs+10_1:1_to=lpo:drc=encompass:sil=2000:fde=unused:sp=const_min:i=444:fd=preordered:crc=on:croc=on:bd=preordered:ss=axioms_0");
    propNZbig14.push("lrs+10_3:58_drc=encompass:sil=256000:tgt=full:bsd=on:sp=reverse_arity:lwlo=on:s2a=on:i=365:s2at=2.0:kws=precedence:bsr=on:irw=on:dpc=on:doe=on:bs=on:br=off:erd=off:s2agt=20:nwc=8.95214440448525:cond=fast:foolp=on:spb=non_intro:sfv=off:crc=on:fde=unused:ins=3_0");
    propNZbig14.push("lrs+10_3:4_to=lpo:drc=encompass:sil=4000:sp=reverse_frequency:i=390:ss=axioms:sgt=16:s2a=on:s2at=3.0:crc=on:bd=off_0");
    propNZbig14.push("lrs+10_1:4_to=lpo:drc=encompass:sil=4000:tgt=full:i=2789:bd=preordered:fd=preordered_0");
    propNZbig14.push("lrs+10_1:3_drc=encompass:sil=256000:tgt=ground:sp=unary_first:i=975:ss=axioms:sgt=10:rawr=on:urr=on:ins=1:plsq=on:dpc=on:spb=intro:sd=4:fsr=off:bs=on:kws=inv_arity:crc=on:nwc=5.0_0");
    propNZbig14.push("lrs+10_1:24_drc=encompass:sil=256000:tgt=full:sp=unary_frequency:spb=non_intro:i=6970:ins=2:fsr=off:kws=precedence:crc=on:croc=on:bsr=unit_only:br=off:ss=included:sgt=16:bd=preordered_0");
    propNZbig14.push("lrs+10_7:24_to=lpo:drc=encompass:sil=128000:fde=unused:sp=const_min:spb=goal:i=522:crc=on:slsq=on:fdi=256:nwc=10.0:dpc=on:ss=included:st=2.0_0");
    propNZbig14.push("lrs+10_1:1024_drc=encompass:sil=8000:tgt=ground:fde=unused:sp=const_min:spb=goal:kmz=on:i=1381:kws=inv_arity:awrs=converge:awrsf=200:crc=on:croc=on_0");
    propNZbig14.push("lrs+10_1:4_to=lpo:drc=encompass:sil=128000:fde=unused:sp=const_min:spb=goal:fd=preordered:i=589:crc=on:slsq=on:slsqr=1,4_0");
    propNZbig14.push("lrs+10_1:4_bsr=on:slsqr=2,7:to=lpo:drc=encompass:sil=16000:tgt=full:sp=unary_first:spb=goal:slsq=on:i=659:slsql=off:ins=2:crc=on:croc=on:rawr=on:nwc=8.7296035496261:erd=off:s2pl=no:cond=fast:plsq=on:sims=off_0");
    propNZbig14.push("lrs+10_1:1_sil=4000:sp=occurrence:i=1397:ss=axioms:st=3.0:sd=2_0");
    propNZbig14.push("lrs+10_15:74_drc=encompass:sil=4000:tgt=full:fde=none:sp=const_min:i=856:kws=inv_frequency:awrs=converge:awrsf=120:rawr=on:nwc=0.9964432792968732:fsr=off:urr=on_0");
    propNZbig14.push("lrs+10_1:28_drc=encompass:sil=256000:tgt=full:spb=intro:i=918:kws=precedence:awrs=converge:awrsf=240:ss=axioms:rawr=on:crc=on:st=3.0:sp=const_frequency_0");
    propNZbig14.push("lrs+10_1:25_to=lpo:drc=encompass:sil=2000:fde=none:sp=const_min:fd=preordered:i=1093_0");
    propNZbig14.push("ott+10_1:2_sil=256000:tgt=ground:sp=reverse_frequency:spb=goal:i=1333:kws=precedence:crc=on_0");
    propNZbig14.push("lrs+10_1:1_drc=encompass:sil=32000:tgt=ground:sp=unary_frequency:lwlo=on:i=23534:crc=on:croc=on:kws=precedence_0");
    propNZbig14.push("dis+10_1:1_sil=256000:nwc=10.0:s2agt=32:s2a=on:i=1724:fde=none:fd=off_0");
    propNZbig14.push("lrs+10_11:1_sil=4000:fde=none:nwc=5.0:st=3.0:i=1762:bd=off:ss=axioms:fd=off_0");
    propNZbig14.push("lrs+10_8:1_drc=encompass:sil=256000:st=3.0:s2a=on:i=3083:s2at=1.2:ss=axioms:sd=15_0");
    propNZbig14.push("lrs+10_1:64_drc=encompass:sil=16000:tgt=full:sp=reverse_frequency:slsq=on:i=4105:kws=precedence:slsql=off:ss=axioms:bs=unit_only:crc=on:spb=goal_0");
    propNZbig14.push("lrs+10_1:4_drc=encompass:sil=32000:tgt=full:fde=unused:sp=const_frequency:nwc=10.0:i=9762:dpc=on:rawr=on:bd=preordered:to=lpo_0");
    propNZbig14.push("lrs+10_1:27_bsr=unit_only:to=lpo:drc=encompass:sil=128000:fde=unused:sp=const_min:spb=goal:fd=preordered:i=9874:bs=on:dpc=on:uhcvi=on:rawr=on:crc=on:er=filter:erape=on:erml=3_0");
    propNZbig14.push("lrs+10_1:4_drc=encompass:sil=16000:tgt=ground:lwlo=on:s2a=on:i=7263:s2at=2.0_0");
    propNZbig14.push("lrs+10_2:3_sil=128000:fde=none:s2a=on:i=13654:s2at=3.0:lwlo=on:bd=off_0");
    propNZbig14.push("lrs+10_1:16_drc=encompass:sil=256000:tgt=full:spb=intro:i=41528:kws=precedence:awrs=converge:awrsf=200:ss=axioms:crc=on:croc=on:st=3.0:sp=const_frequency_0");
    propNZbig14.push("dis+10_1:32_drc=encompass:sil=256000:tgt=ground:sp=const_frequency:spb=goal:i=32120:kws=precedence:bd=off:dpc=on:crc=on:s2a=on:s2at=3.0_0");
    propNZbig14.push("ott+10_1:6_drc=encompass:sil=512000:tgt=ground:fde=unused:sp=const_min:spb=goal:nwc=1.1:i=95210:kws=precedence:dpc=on_0");
    propNZbig14.push("lrs+10_1:32_sil=64000:tgt=full:sp=frequency:lwlo=on:i=51758:crc=on:croc=on_0");
    propNZbig14.push("lrs+10_2:23_drc=encompass:sil=256000:tgt=full:s2a=on:i=126830:s2at=2.0:crc=on:dpc=on_0");
    propNZbig14.push("lrs+10_1:24_bsr=unit_only:to=lpo:drc=encompass:sil=128000:fde=unused:sp=const_min:spb=goal:fd=preordered:i=67476:bs=on:dpc=on:rawr=on:crc=on:er=filter:erape=on:nwc=3.0:ss=axioms:st=6.0:urr=ec_only_0");
    propNZbig14.push("lrs+10_1:3_drc=encompass:sil=256000:tgt=full:fd=preordered:s2a=on:i=85601:s2at=4.0_0");

    // total_instr 925697
    // len(covered) 138

  } else {
    // The FOF division: First-Order Form theorems (axioms with a provable conjecture).

    Schedule fne;

    fne.push("lrs+21_1:32_anc=all:to=lpo:sil=256000:plsq=on:plsqr=32,1:sp=occurrence:sos=on:plsql=on:sac=on:newcnf=on:i=222662:add=off:fsr=off:rawr=on_0");
    fne.push("lrs+1011_4:1_sil=256000:rp=on:newcnf=on:i=257909:aac=none:gsp=on_0");
    fne.push("dis+1002_1:1_tgt=full:sos=on:rp=on:sac=on:i=258102:ss=axioms:sd=3:cond=fast:add=off:abs=on:fde=none:sil=256000_0");

    fne.push("lrs+21_8:1_to=lpo:sil=2000:sp=frequency:spb=units:s2a=on:s2pl=no:i=103:sd=2:ss=included:fsr=off:fs=off_0");
    fne.push("lrs+1011_4:1_to=lpo:drc=off:sil=8000:sp=frequency:abs=on:urr=on:lsd=10:nwc=5.0:s2agt=4:newcnf=on:st=5.0:s2a=on:i=107:ss=axioms:aac=none:br=off:bd=preordered_0");
    fne.push("lrs+10_8:1_to=lpo:drc=encompass:sil=4000:sos=on:urr=on:newcnf=on:i=116:sd=2:nm=2:ss=axioms:sgt=32:sup=off:bd=off_0");
    fne.push("lrs+1011_1:13_sil=2000:tgt=full:sims=off:sp=occurrence:abs=on:newcnf=on:i=104:nm=4:ss=axioms:rawr=on:amm=off_0");
    fne.push("lrs+2_1:1_sil=4000:plsqc=4:plsq=on:plsqr=2,1:rp=on:i=110:nm=10:fde=unused:ep=RS:slsq=on:slsql=off:slsqr=1,8:erd=off_0");
    fne.push("lrs+1011_1:1_sil=8000:sp=occurrence:nwc=10.0:st=1.5:i=319:ss=axioms:sgt=4_0");
    fne.push("ott+1010_1:3_sil=8000:tgt=full:sp=occurrence:urr=on:br=off:nicw=on:i=121:sd=2:ss=axioms:sgt=8:gsp=on_0");
    fne.push("lrs+1002_1:1_sil=16000:sp=occurrence:sos=on:urr=on:i=440:ss=axioms:sgt=10_0");
    fne.push("lrs+1011_1:128_sil=2000:i=230:fsr=off:nwc=2.0_0");
    fne.push("dis+2_1:3_sil=8000:nwc=5.0:st=3.0:s2a=on:i=119:s2at=2.5:sd=3:nm=2:ss=axioms_0");
    fne.push("lrs+11_1:32_sil=2000:sp=occurrence:lsd=20:rp=on:i=113:sd=1:nm=0:av=off:ss=included:nwc=10.0:flr=on_0");
    fne.push("dis-1010_1:4_sil=2000:tgt=ground:i=128:sd=2:nm=6:av=off:gsp=on:ss=axioms:nwc=10.0_0");
    fne.push("lrs+4_1:8_sil=32000:abs=on:nwc=5.0:updr=off:i=963:nm=6:plsq=on:plsql=on:plsqc=1:plsqr=2,1_0");
    fne.push("dis+1002_1:128_to=lpo:sil=2000:fd=preordered:i=204:fsr=off:av=off:sos=on:s2a=on_0");
    fne.push("lrs+1011_1:1_sil=2000:plsq=on:plsqr=32,1:fs=off:gs=on:i=516:nm=0:fsr=off:rawr=on:nwc=0.5744209687727792_0");
    fne.push("lrs+21_9739:1048576_drc=off:sil=128000:tgt=ground:spb=non_intro:s2a=on:i=1028:s2at=2.0:kws=precedence:sp=reverse_arity:awrs=decay:awrsf=270_0");
    fne.push("ott-1011_3:2_to=lpo:drc=off:sil=2000:sims=off:sos=on:lma=on:spb=goal_then_units:lcm=predicate:fd=preordered:rp=on:newcnf=on:avsq=on:i=340:ins=1:fsr=off:avsqc=4:aac=none:plsq=on:plsqc=1:plsqr=32,1:fs=off_0");
    fne.push("dis+1011_3:8_bsr=unit_only:slsqr=1,16:sil=2000:plsq=on:plsqr=296,127:sp=reverse_frequency:lsd=5:nwc=10.0:slsqc=3:slsq=on:st=3.0:i=225:s2at=4.5:sd=4:slsql=off:nm=16:ins=5:ss=axioms:sgt=20:rawr=on:urr=ec_only:to=lpo_0");
    fne.push("dis+1011_1:1_bsr=unit_only:slsqr=1,2:sil=2000:plsqc=1:plsq=on:plsqr=32,1:lsd=20:plsql=on:slsqc=1:slsq=on:i=732:slsql=off:nm=2:uhcvi=on:rawr=on:fsr=off:avsq=on:avsqr=9387,262144_0");
    fne.push("dis+1011_3:1_sil=64000:lsd=10:slsq=on:s2a=on:i=231:ep=RS:nm=2:ss=axioms_0");
    fne.push("lrs-32_1:1024_sil=8000:sos=on:i=752:nm=4:updr=off_0");
    fne.push("lrs+10_1:2_sil=2000:spb=units:nwc=10.0:flr=on:i=1025:fsr=off:ss=axioms_0");
    fne.push("lrs+1011_1:128_bsr=unit_only:sil=4000:plsq=on:plsqr=27,2:lsd=5:plsql=on:nwc=3.0:i=1583:rawr=on_0");
    fne.push("lrs+1010_1:8_sil=4000:sos=on:urr=on:rnwc=on:nwc=10.0:i=398:sup=off:kws=frequency_0");
    fne.push("dis+1002_1:85_sil=4000:nwc=10.0:i=404:s2at=2.0:av=off:slsq=on:slsqc=2:fsr=off_0");
    fne.push("lrs+1010_1:32_bsr=on:sil=4000:i=483:nm=2:gsp=on_0");
    fne.push("lrs+1011_4:1_sil=2000:sp=const_max:sos=on:bce=on:avsq=on:i=499:sd=4:kws=inv_frequency:avsqr=1,16:nm=2:ss=axioms:uhcvi=on:fs=off:fsr=off:s2a=on:etr=on:anc=none:avsqc=5_0");
    fne.push("dis+11_1:64_bsr=unit_only:to=lpo:sil=16000:sp=frequency:flr=on:cond=on:i=560:awrs=converge:awrsf=200:rawr=on:sup=off:abs=on_0");
    fne.push("lrs+1011_1:32_sil=2000:lsd=10:rp=on:newcnf=on:i=883:fsr=off:fs=off_0");
    fne.push("lrs+1_1:1024_slsqr=7,4:sil=8000:sp=frequency:urr=on:nwc=2.0:slsqc=3:slsq=on:i=3281:slsql=off:nm=2:av=off:rawr=on:updr=off_0");
    fne.push("lrs+1011_1:10_sil=2000:lsd=100:rp=on:sac=on:s2a=on:i=1175:nm=3:rawr=on:nicw=on_0");
    fne.push("lrs+1011_1:1024_anc=all_dependent:sil=4000:plsqc=3:plsq=on:sp=unary_first:lsd=10:bce=on:i=2959:bs=unit_only:afp=50:nm=4:afq=3.79765_0");
    fne.push("lrs+10_23:15_sil=2000:plsqc=1:plsq=on:plsqr=4106395,32768:plsql=on:nwc=3.0:flr=on:newcnf=on:i=2105:kws=precedence:fsr=off:ss=included_0");
    fne.push("dis+1011_1:20_sil=16000:plsq=on:plsqr=62867,524288:sp=occurrence:lsd=20:rp=on:newcnf=on:i=3384:aac=none:rawr=on:uhcvi=on:fsr=off:fdi=5:alpa=false:anc=none_0");
    fne.push("dis-1002_12_add=off:bs=on:bsr=on:cond=on:flr=on:gsp=on:gs=on:gsem=off:nm=4:sims=off:tgt=ground:i=3654_0");
    fne.push("dis+22_1:8_sil=128000:abs=on:alpa=true:sac=on:i=10575:nm=2:amm=off:sup=off_0");
    fne.push("dis+3_1024_av=off:fsr=off:gsp=on:lcm=predicate:nm=4:sos=all:sp=weighted_frequency:i=22214_0");
    fne.push("lrs+1011_1:64_sil=16000:urr=on:br=off:i=8671:nm=2:gsp=on:fdi=1_0");
    fne.push("dis+20_1:1_sil=32000:i=9754:nm=2:gsp=on:rawr=on:plsq=on:plsqr=2,7:lma=on:rp=on_0");
    fne.push("lrs-1011_10:13_sil=32000:tgt=ground:plsq=on:plsqr=768,109:abs=on:urr=full:bce=on:i=11447:bs=unit_only:kws=precedence:awrs=converge:awrsf=500:rawr=on:lwlo=on:sp=frequency_0");

    // total_instr 830728
    // len(covered) 1262

    Schedule feqAtomsG18000;

    feqAtomsG18000.push("lrs-1002_12164383:1048576_anc=all_dependent:bsr=on:sil=256000:i=187735:bs=unit_only:awrs=decay:awrsf=132:ep=R:amm=off:uhcvi=on:abs=on_0");
    feqAtomsG18000.push("lrs-1011_8:1_plsq=on:urr=on:nwc=10.0:sac=on:newcnf=on:s2a=on:i=235504:sd=2:ss=axioms:sil=256000:kws=inv_frequency:gsp=on_0");

    feqAtomsG18000.push("dis+1011_1:1_sil=16000:nwc=7.0:s2agt=64:s2a=on:i=1102:ss=axioms:sgt=8:lsd=50:sd=7_0");
    feqAtomsG18000.push("dis+1010_1:1_drc=off:sil=32000:rp=on:cond=fast:i=886:av=off:newcnf=on:bd=off:sfv=off:plsq=on:plsqr=1,32:erd=off_0");
    feqAtomsG18000.push("lrs+1010_1:1_to=lpo:sil=8000:sos=on:spb=goal:rp=on:i=1785:nm=6:ss=included:sd=1_0");
    feqAtomsG18000.push("ott-1010_16:1_bsr=unit_only:sil=64000:sos=on:urr=on:sac=on:i=3480:sd=2:kws=inv_frequency:ins=4:ss=axioms:br=off_0");
    feqAtomsG18000.push("lrs+1011_1:1_sil=8000:nicw=on:i=1004:sd=1:ss=axioms:sgt=64_0");
    feqAtomsG18000.push("lrs+1002_1:4_sil=2000:fde=unused:plsq=on:plsqr=32,1:sos=on:bce=on:i=307:sd=1:ss=included:rawr=on_0");
    feqAtomsG18000.push("dis-1010_1:1_bsr=unit_only:to=lpo:sil=256000:fde=none:plsq=on:plsqr=205,29:sp=occurrence:sos=on:abs=on:newcnf=on:st=6.0:i=5784:sd=2:bd=off:amm=off:ss=axioms:rawr=on_0");
    feqAtomsG18000.push("lrs+2_1:1_sil=256000:plsq=on:plsqr=17685,131072:sos=on:lcm=reverse:i=311:av=off:ss=axioms:ep=RST:sd=2_0");
    feqAtomsG18000.push("lrs+1011_1:1_sil=8000:sp=occurrence:nwc=10.0:i=1126:ss=axioms:sgt=8_0");
    feqAtomsG18000.push("ott-1011_11873131:1048576_drc=encompass:fde=unused:plsq=on:plsqr=3,59:sp=frequency:urr=on:nwc=13.753829265569435:sac=on:st=1.5:s2a=on:i=14494:sd=3:afp=10:bd=preordered:afq=2.759712924428805:ss=axioms:bs=on:sil=256000:kws=inv_frequency:bce=on:s2agt=8:sgt=8:awrs=decay:awrsf=80:nm=32:rawr=on_0");
    feqAtomsG18000.push("lrs+2_1:1_sil=2000:tgt=ground:sos=on:i=867:sd=1:ss=included:to=lpo:plsq=on:plsqr=32,1_0");
    feqAtomsG18000.push("dis-1010_1:8_sil=256000:i=7640:nm=16:av=off:erd=off:sfv=off:fd=off:bd=off_0");
    feqAtomsG18000.push("lrs-1010_2:1_sil=4000:tgt=ground:sos=on:erd=off:bce=on:st=4.5:i=365:sd=1:kws=inv_frequency:ss=axioms:sgt=100:rawr=on:avsq=on:avsqr=17,12:plsq=on:plsqr=25,62:anc=all_dependent_0");
    feqAtomsG18000.push("lrs-1010_1:1_to=lpo:sil=2000:i=369:sd=2:ss=axioms:av=off:sos=on_0");
    feqAtomsG18000.push("dis-1011_1:1_sil=8000:nwc=5.0:slsqc=2:slsq=on:s2a=on:i=659:slsql=off:s2agt=16:ss=axioms_0");
    feqAtomsG18000.push("lrs+1011_1:1024_slsqr=1,8:sil=2000:rp=on:nwc=10.0:newcnf=on:slsq=on:st=1.5:s2a=on:i=400:sd=1:awrs=converge:awrsf=390:ep=RST:ss=axioms:sac=on_0");
    feqAtomsG18000.push("dis-1010_1:1024_sil=64000:tgt=full:i=11462:nm=0:av=off:ep=RST:fsr=off:bs=unit_only_0");
    feqAtomsG18000.push("dis+2_8:1_sil=2000:fde=unused:s2a=on:i=417:sd=2:ss=included_0");
    feqAtomsG18000.push("lrs+21_1:1_sil=16000:nwc=19.4924:s2agt=16:s2a=on:i=1369:sd=2:bd=off:ss=axioms:sgt=8:fs=off:fsr=off_0");
    feqAtomsG18000.push("dis-1011_1785:1048576_bsr=unit_only:sil=4000:tgt=ground:plsqc=1:plsq=on:plsqr=125493,524288:sp=frequency:spb=goal:plsql=on:nwc=2.32086:updr=off:newcnf=on:cond=fast:st=2:s2a=on:i=1705:s2at=4:bd=off:nm=3:ins=3:aer=off:uhcvi=on:afr=on:ss=axioms:sgt=20:rawr=on:fsr=off_0");
    feqAtomsG18000.push("dis-1010_8:1_sil=64000:sp=occurrence:sos=on:st=2.0:i=789:sd=3:bd=off:ss=axioms:acc=model:to=lpo:sup=off:fs=off:fsr=off:sgt=32_0");
    feqAtomsG18000.push("dis+1010_2:1_sil=2000:sos=on:rp=on:st=1.5:i=1523:ins=7:fsr=off:amm=off:ss=axioms:sd=4:fs=off:kws=inv_frequency_0");
    feqAtomsG18000.push("ott+10_107421:1048576_to=lpo:drc=off:sil=4000:fde=none:sos=on:lma=on:spb=intro:gs=on:nwc=24.2524:gsem=off:i=504:sd=3:afp=40000:awrs=decay:awrsf=1166:nm=6:afq=1.99252:uhcvi=on:ss=axioms:rawr=on:sp=const_max:add=off_0");
    feqAtomsG18000.push("lrs+1002_1:1_to=lpo:sil=4000:sos=on:i=522:sd=1:ss=included_0");
    feqAtomsG18000.push("lrs+11_1:1_to=lpo:sil=64000:sp=occurrence:nwc=2.0:st=6.0:s2a=on:i=550:s2at=5.0:sd=1:nm=3:gsp=on:ss=axioms:fsr=off_0");
    feqAtomsG18000.push("dis+33_1930041:1048576_sil=4000:tgt=ground:plsqc=1:plsq=on:plsqr=4356867,524288:sp=frequency:sos=on:lma=on:spb=intro:lcm=reverse:rnwc=on:plsql=on:nwc=24.1115:sac=on:cond=fast:st=1.5:i=1480:bs=on:sd=2:kws=precedence:nm=40:uhcvi=on:ss=axioms:rawr=on:bd=off:nicw=on_0");
    feqAtomsG18000.push("lrs-10_1:1_sil=16000:sos=on:st=3.0:i=2917:sd=2:ep=RST:fsr=off:ss=axioms_0");
    feqAtomsG18000.push("dis+1011_16:1_sil=16000:tgt=full:nwc=10.0:alpa=random:sac=on:avsq=on:i=12988:sd=1:kws=inv_frequency:ss=included_0");
    feqAtomsG18000.push("dis+10_52093:131072_drc=off:sil=2000:tgt=ground:irw=on:foolp=on:lma=on:urr=ec_only:nwc=5.20774:st=1.5:i=1235:sd=2:kws=inv_frequency:nm=7:ins=3:av=off:uhcvi=on:ss=axioms:rawr=on_0");
    feqAtomsG18000.push("dis-21_1:1_drc=encompass:sos=on:urr=ec_only:i=2965:ins=1:av=off:ss=axioms:fde=none:sd=3:bsr=on:sil=8000:nm=3_0");
    feqAtomsG18000.push("dis+34_1:1_sil=8000:tgt=full:plsqc=1:plsq=on:plsqr=32,1:rp=on:nwc=10.0:newcnf=on:i=686:sd=1:av=off:ss=axioms_0");
    feqAtomsG18000.push("dis+1011_16:1_lsd=20:bce=on:i=2880:ep=R:ins=1:ss=axioms:newcnf=on:sos=on:sil=32000:rp=on:fsr=off:fs=off:awrs=converge:sd=2_0");
    feqAtomsG18000.push("lrs+10_1:1_sos=on:abs=on:s2agt=16:slsq=on:st=1.5:i=1509:ep=R:fsr=off:ss=axioms:rawr=on:s2a=on:fs=off:sd=4:sil=8000_0");
    feqAtomsG18000.push("ott-1010_3376641:1048576_anc=none:to=lpo:sil=4000:tgt=ground:fde=unused:sp=unary_frequency:sos=on:spb=intro:lcm=predicate:fd=preordered:st=3.0:i=807:sd=1:bd=off:nm=3:ins=2:fsr=off:uhcvi=on:fdi=64:ss=included:sgt=100:newcnf=on:nwc=3.871969461363868_0");
    feqAtomsG18000.push("dis+1011_1:2_sil=2000:tgt=ground:rp=on:newcnf=on:st=7.0:i=818:sd=1:nm=0:ss=axioms:sgt=32_0");
    feqAtomsG18000.push("ott+1002_2835555:1048576_to=lpo:sil=2000:sos=on:fs=off:nwc=10.3801:avsqc=3:updr=off:avsq=on:st=2:s2a=on:i=822:s2at=3:afp=10000:aac=none:avsqr=13357983,1048576:awrs=converge:awrsf=460:bd=off:nm=13:ins=2:fsr=off:amm=sco:afq=1.16719:ss=axioms:rawr=on:fd=off_0");
    feqAtomsG18000.push("dis+1011_38921:131072_bsr=on:drc=encompass:sil=8000:tgt=full:sp=frequency:sos=on:spb=goal:lcm=reverse:nwc=23.4974:newcnf=on:cond=fast:st=1.5:i=4682:sd=2:bd=preordered:nm=16:av=off:ss=axioms:sgt=10:rawr=on:bsd=on:kws=arity_squared:rp=on:ins=1_0");
    feqAtomsG18000.push("dis+2_1:3_sil=8000:nwc=5.0:st=3.0:s2a=on:i=885:s2at=2.5:sd=3:nm=2:ss=axioms_0");
    feqAtomsG18000.push("lrs+10_1:1_sil=4000:sos=on:acc=on:st=2.5:i=918:bd=off:fsr=off:ss=axioms:sd=3:flr=on:fs=off:fd=off_0");
    feqAtomsG18000.push("lrs+21_1:1_sil=16000:sos=all:lma=on:i=2583:sd=1:ep=R:ss=axioms_0");
    feqAtomsG18000.push("dis-1011_3:1_sil=32000:fde=none:sos=all:nwc=5.0:i=26266:ep=R:aac=none_0");
    feqAtomsG18000.push("dis+1002_1:1_sil=16000:tgt=ground:sac=on:i=8303:sd=2:aac=none:ss=axioms:nwc=10.0_0");
    feqAtomsG18000.push("lrs-1010_1:128_tgt=ground:si=on:plsq=on:plsqr=2087559,524288:sos=on:st=1.5:i=1932:sd=2:rtra=on:ss=included:sil=128000:ins=1:gsp=on:anc=all_dependent_0");
    feqAtomsG18000.push("lrs+1011_1:8_to=lpo:sil=2000:sos=all:urr=ec_only:br=off:nwc=10.0:newcnf=on:st=3.0:i=1083:sd=3:bd=off:nm=2:fdi=50:ss=axioms:sfv=off:sac=on_0");
    feqAtomsG18000.push("lrs+4_5:1_anc=all_dependent:to=lpo:tgt=ground:sp=frequency:sos=on:spb=non_intro:s2a=on:i=2485:sd=2:aac=none:awrs=decay:awrsf=500:bd=off:fsr=off:amm=off:ss=axioms:fs=off:sil=32000_0");
    feqAtomsG18000.push("lrs+10_1:2_bsr=unit_only:sil=64000:sos=on:s2agt=64:sac=on:s2a=on:s2pl=no:i=2541:sd=1:kws=inv_precedence:nm=3:ss=included:bd=off:avsq=on:avsqr=1,16_0");
    feqAtomsG18000.push("ott+21_1:1_av=off:lcm=reverse:lma=on:sd=2:sos=all:ss=axioms:st=1.5:si=on:rawr=on:rtra=on:i=1374_0");
    feqAtomsG18000.push("lrs+1011_1:1_sil=16000:sos=on:i=3167:sd=2:ss=axioms:sgt=16_0");
    feqAtomsG18000.push("lrs+2_1:1024_to=lpo:drc=off:sil=128000:urr=on:nwc=3.0:i=1636:sd=1:awrs=converge:awrsf=270:nm=4:ins=1:ss=axioms:gsp=on:bd=preordered_0");
    feqAtomsG18000.push("lrs+1011_2:3_sil=16000:sos=on:rp=on:newcnf=on:lwlo=on:st=1.5:i=1655:sd=2:bd=off:nm=2:fsr=off:gsp=on:ss=axioms:bce=on:anc=all:sac=on_0");
    feqAtomsG18000.push("dis+10_8:1_to=lpo:sil=64000:tgt=ground:fde=unused:sp=const_max:sos=all:spb=goal:s2a=on:i=2033:sd=4:nm=32:ss=axioms:fs=off:fsr=off:sfv=off:alpa=true_0");
    feqAtomsG18000.push("dis+10_1:7_si=on:nwc=3.0:random_seed=871647488:st=3.0:s2a=on:i=5899:s2at=2.5:sd=2:awrs=converge:awrsf=500:nm=2:rtra=on:ss=included:rawr=on:sil=64000_0");
    feqAtomsG18000.push("dis-1002_1:1_to=lpo:sil=128000:sp=unary_first:abs=on:rp=on:nwc=5.0:flr=on:st=1.5:s2a=on:i=2097:sd=7:nm=4:fdi=5:ss=included_0");
    feqAtomsG18000.push("lrs+11_1:128_st=2.0:i=129712:ss=axioms:to=lpo:sil=256000:sd=15:ep=RS_0");
    feqAtomsG18000.push("lrs+1002_1624159:1048576_to=lpo:sil=64000:fde=none:sp=frequency:sos=on:spb=non_intro:nwc=15.7653:s2agt=30:avsqc=2:avsq=on:s2a=on:i=2438:s2at=3:sd=2:avsqr=6990209,1048576:awrs=decay:awrsf=762:bd=off:nm=4:ss=included:fd=off:rawr=on:fs=off:fsr=off:aac=none_0");
    feqAtomsG18000.push("dis+1002_1:1_tgt=full:sos=on:rp=on:sac=on:i=12801:ss=axioms:sd=3:cond=on:add=off:abs=on:fde=none:sil=256000:rawr=on:newcnf=on:bsd=on:afp=1000:afq=1.7_0");
    feqAtomsG18000.push("lrs+35_8:1_sos=all:s2a=on:i=5191:sd=2:ss=axioms:sil=128000:fde=none:gsp=on:av=off:nm=4:sfv=off_0");
    feqAtomsG18000.push("dis+21_1:1_drc=encompass:sos=on:urr=ec_only:i=5645:ins=1:av=off:ss=axioms:gsp=on:sd=3:sil=8000:nm=3_0");
    feqAtomsG18000.push("lrs+1011_1:3_sil=64000:sos=on:lsd=20:newcnf=on:st=2.0:s2a=on:i=3126:sd=1:nm=2:ss=included:s2agt=32:to=lpo:fd=off:bd=off:nicw=on:rp=on_0");
    feqAtomsG18000.push("dis+1011_1:1_drc=off:sil=16000:tgt=full:fde=unused:nwc=2.0:st=1.5:i=6739:sd=3:fsr=off:ss=axioms:nm=2_0");
    feqAtomsG18000.push("dis-21_1:4_to=lpo:sil=8000:tgt=ground:sp=unary_first:lcm=reverse:alpa=random:i=3443:sd=1:awrs=converge:awrsf=500:fsr=off:ss=axioms_0");
    feqAtomsG18000.push("lrs-1011_8:1_sil=16000:sos=all:i=3472:sd=1:ep=R:ss=axioms_0");
    feqAtomsG18000.push("ott-3_2:1_acc=on:add=large:anc=none:fde=none:gsp=on:irw=on:nm=0:s2a=on:sd=4:sos=on:ss=axioms:st=1.2:urr=on:si=on:rawr=on:rtra=on:i=10677_0");
    feqAtomsG18000.push("lrs-1010_1:4_sil=256000:sp=occurrence:sos=on:s2a=on:i=43014:sd=1:kws=precedence:bd=off:ins=3:ss=included:sfv=off:amm=off_0");
    feqAtomsG18000.push("ott+1010_1:3_sil=8000:tgt=full:sp=occurrence:urr=on:br=off:nicw=on:i=3725:sd=2:ss=axioms:sgt=8:gsp=on_0");
    feqAtomsG18000.push("ott-1011_16:1_urr=on:nwc=10.0:sac=on:s2a=on:i=18730:sd=2:ss=axioms:bsr=on:sil=256000:kws=inv_frequency:anc=all:fs=off:fsr=off:alpa=true_0");
    feqAtomsG18000.push("lrs+2_3:1_to=lpo:sil=256000:irw=on:fde=unused:sp=unary_first:bce=on:nwc=6.0:s2agt=30:newcnf=on:s2a=on:i=18973:nm=2_0");
    feqAtomsG18000.push("lrs+1_4:1_cond=fast:fde=unused:lcm=predicate:nm=4:s2a=on:sd=3:sos=on:ss=axioms:st=2.0:sil=16000:si=on:rawr=on:rtra=on:i=4988_0");
    feqAtomsG18000.push("lrs+1011_2:1_tgt=full:sos=on:urr=full:nwc=5.0:st=5.0:i=5744:sd=1:kws=precedence:ss=axioms:sil=128000:rnwc=on:sac=on_0");
    feqAtomsG18000.push("dis+1010_5:1_sil=64000:sp=const_min:sos=on:acc=model:i=5912:kws=precedence:bd=off:nm=20:alpa=random:ss=axioms_0");
    feqAtomsG18000.push("dis+1011_11:32_to=lpo:drc=off:sil=16000:sp=frequency:abs=on:lsd=10:rp=on:nwc=19.9405:newcnf=on:i=6939:sd=2:nm=3:ins=2:ss=axioms:rawr=on:bce=on:bd=preordered:fsr=off_0");
    feqAtomsG18000.push("lrs+11_1:12_to=lpo:sil=128000:sp=const_min:i=18088:ss=included:sgt=16:av=off:fsd=on:nm=16_0");
    feqAtomsG18000.push("lrs-1010_1:1_drc=off:sil=16000:sos=on:flr=on:i=9467:bd=off:nm=6:ss=included:alpa=false:fs=off:fsr=off_0");
    feqAtomsG18000.push("dis-1011_2:7_sil=16000:tgt=ground:lsd=100:rp=on:nwc=5.0:st=1.5:i=9563:sd=2:ins=1:av=off:ss=axioms:sgt=100_0");
    feqAtomsG18000.push("dis+1002_1:1_tgt=full:sos=on:rp=on:sac=on:i=45185:ss=axioms:sd=3:cond=fast:add=off:abs=on:fde=none:sil=256000_0");
    feqAtomsG18000.push("lrs+1011_8:1_sil=128000:tgt=ground:fde=unused:sp=frequency:nwc=5.0:lwlo=on:i=11807:awrs=converge:awrsf=1385:av=off_0");
    feqAtomsG18000.push("dis+1011_3:1_sil=256000:tgt=ground:sac=on:i=27305:sd=1:ss=included_0");
    feqAtomsG18000.push("lrs+1011_1:1_tgt=full:sos=on:spb=goal_then_units:urr=full:st=5.5:i=14604:sd=1:kws=precedence:ss=axioms:nicw=on:sil=128000_0");
    feqAtomsG18000.push("lrs+10_2:29_sil=64000:irw=on:fde=none:sp=unary_frequency:sos=on:fd=preordered:st=2.0:i=31370:sd=2:kws=frequency:bd=off:nm=6:fsr=off:ss=included:rawr=on:lma=on:sgt=20:cond=fast_0");
    feqAtomsG18000.push("lrs-1011_6:1_sos=all:s2a=on:i=114836:sd=2:ss=included:bd=off:sil=128000:fde=none:abs=on:amm=off:gsp=on:sp=const_min:cond=fast:avsq=on:avsqc=1:avsqr=11,2:nm=5:sfv=off:plsq=on:plsqr=199691,1048576_0");
    feqAtomsG18000.push("lrs+2_1:1_anc=all_dependent:bsr=unit_only:sil=32000:i=17658:bs=on:alpa=true_0");
    feqAtomsG18000.push("lrs-1002_1:1_anc=all:sil=64000:tgt=full:sos=on:st=1.5:i=25368:sd=2:kws=inv_frequency:aac=none:fsr=off:ss=axioms:abs=on:fs=off_0");
    feqAtomsG18000.push("dis+1011_3:7_to=lpo:sos=on:spb=goal_then_units:abs=on:lsd=20:st=1.5:i=85957:sd=2:aac=none:awrs=decay:bd=off:ss=axioms:sgt=32:flr=on:sil=256000:nm=26_0");
    feqAtomsG18000.push("lrs+1011_1:1_drc=encompass:sil=128000:tgt=ground:i=58209:kws=frequency:ss=axioms:lwlo=on:fde=unused:sp=reverse_arity_0");

    // total_instr 1341991
    // len(covered) 867

    Schedule feqAtomsG2800;

    feqAtomsG2800.push("lrs+10_1:628_anc=all_dependent:bsr=unit_only:sil=256000:sp=frequency:i=136310:newcnf=on_0");
    feqAtomsG2800.push("lrs+2_3:1_to=lpo:sil=256000:irw=on:fde=unused:sp=unary_first:bce=on:nwc=6.0:s2agt=30:newcnf=on:s2a=on:i=140573:nm=2_0");

    feqAtomsG2800.push("lrs+11_1:12_to=lpo:sil=128000:sp=const_min:i=103397:ss=included:sgt=16:av=off:fsd=on:nm=16_0");
    feqAtomsG2800.push("dis+2_1:50_sil=256000:flr=on:sac=on:i=218245:fsr=off:uhcvi=on_0");

    feqAtomsG2800.push("lrs-1010_1:1_sil=2000:i=250:sd=1:ss=axioms:sgt=32:sos=on_0");
    feqAtomsG2800.push("lrs-1011_8:1_sil=16000:sos=all:i=346:sd=1:ep=R:ss=axioms_0");
    feqAtomsG2800.push("lrs+1002_1:1_to=lpo:sil=2000:sp=frequency:sos=on:st=3.0:i=282:sd=2:ss=axioms_0");
    feqAtomsG2800.push("lrs+1010_1:1_sil=8000:sp=occurrence:urr=on:br=off:st=1.2:i=125:sd=7:ss=axioms:sgt=16_0");
    feqAtomsG2800.push("lrs+1010_1:1_to=lpo:sil=2000:sos=on:fd=off:i=402:bd=off_0");
    feqAtomsG2800.push("lrs+2_5:1_sil=2000:sos=on:acc=on:urr=on:alpa=false:i=325:sd=1:bd=off:nm=32:ss=axioms:br=off:sup=off:bs=on_0");
    feqAtomsG2800.push("lrs+1011_1:1_to=lpo:drc=encompass:sil=4000:plsq=on:plsqr=32,1:sp=occurrence:sos=on:erd=off:urr=on:lsd=100:i=267:sd=1:nm=2:ss=axioms:flr=on:sup=off_0");
    feqAtomsG2800.push("lrs+33_1:1_sil=4000:sp=reverse_frequency:sos=all:i=156:sd=2:bd=off:nm=2:av=off:fsr=off:ss=axioms:sgt=10:rawr=on:sup=off:to=lpo:fs=off_0");
    feqAtomsG2800.push("dis+1011_1:1_to=lpo:sil=4000:sp=const_max:sos=all:spb=goal:st=1.5:i=200:av=off:ss=axioms:sfv=off:bd=off:sd=2:fd=off_0");
    feqAtomsG2800.push("dis-1010_1:4_sil=2000:tgt=ground:fd=off:i=203:sd=1:nm=4:av=off:ss=axioms:sgt=64:newcnf=on_0");
    feqAtomsG2800.push("lrs+1002_1:8_sil=4000:sos=on:nicw=on:st=2.5:i=1027:ss=included:sd=7:ep=RS:erd=off_0");
    feqAtomsG2800.push("ott+10_107421:1048576_to=lpo:drc=off:sil=4000:fde=none:sos=on:lma=on:spb=intro:gs=on:nwc=24.2524:gsem=off:i=316:sd=3:afp=40000:awrs=decay:awrsf=1166:nm=6:afq=1.99252:uhcvi=on:ss=axioms:rawr=on:sp=const_max:add=off_0");
    feqAtomsG2800.push("lrs+10_8:1_bsr=unit_only:sil=4000:urr=on:lcm=reverse:rp=on:i=426:sd=1:nm=6:av=off:ss=included:sup=off:sos=on_0");
    feqAtomsG2800.push("dis+1011_1:1_sil=16000:nwc=7.0:s2agt=64:s2a=on:i=260:ss=axioms:sgt=8:lsd=50:sd=7_0");
    feqAtomsG2800.push("lrs+2_1:1_drc=encompass:sil=2000:urr=on:nwc=10.0:i=160:sd=3:fsr=off:ss=axioms:fd=preordered:bd=off:sup=off_0");
    feqAtomsG2800.push("dis+11_5603931:1048576_bsr=on:sfv=off:slsqr=176855,1048576:sil=2000:plsq=on:plsqr=4348351,262144:sp=occurrence:spb=units:lcm=predicate:fd=off:nwc=1.37809:s2agt=10:slsq=on:s2a=on:i=462:bs=unit_only:sd=3:kws=arity_squared:slsql=off:bd=off:nm=26:av=off:ss=axioms:sgt=15:fsr=off_0");
    feqAtomsG2800.push("dis+1010_3:2_sil=4000:plsq=on:s2agt=100:sac=on:s2a=on:i=2185:s2at=2.0:ep=RS:tgt=full_0");
    feqAtomsG2800.push("dis+1002_1:2_to=lpo:sil=2000:sos=on:abs=on:newcnf=on:i=308:sd=1:bd=off:ss=included:rawr=on:sp=const_frequency:fsr=off:fs=off_0");
    feqAtomsG2800.push("dis+1010_1:1_to=lpo:sil=2000:plsq=on:plsqr=32,1:sos=on:spb=goal:rp=on:i=336:bd=off:ins=4:ss=axioms:sgt=32:acc=on:fde=none_0");
    feqAtomsG2800.push("dis+1010_16550053:1048576_to=lpo:ccuc=small_ones:sil=4000:fde=none:plsq=on:avsql=on:plsqr=34063,1048576:sp=const_min:sos=on:acc=model:plsql=on:nwc=10.3787:avsq=on:i=349:sd=1:avsqr=1084175,1048576:nm=0:amm=off:ss=axioms:bce=on:rawr=on:sup=off:bd=off_0");
    feqAtomsG2800.push("lrs+2_1:1_sil=2000:sos=all:st=5.0:i=193:bd=off:av=off:ss=axioms:sd=2:sup=off_0");
    feqAtomsG2800.push("lrs+1002_1:1_sil=64000:sos=on:urr=ec_only:flr=on:st=3.0:i=632:sd=1:ep=RS:nm=16:ss=axioms_0");
    feqAtomsG2800.push("lrs+1011_4801913:1048576_sfv=off:sil=2000:plsqc=1:plsq=on:plsqr=98277,1048576:etr=on:sp=const_max:lma=on:erape=on:urr=full:rp=on:nwc=23.4614:lwlo=on:st=2.5:i=440:add=large:bs=unit_only:sd=2:kws=inv_arity_squared:awrs=converge:awrsf=951:nm=17:amm=sco:ss=axioms:er=filter:sgt=50:rawr=on:anc=none_0");
    feqAtomsG2800.push("lrs-1011_4:1_bsr=unit_only:sil=4000:sp=occurrence:lsd=20:newcnf=on:i=730:kws=inv_arity_squared:awrs=converge:rawr=on:rp=on:alpa=false:nwc=3.0_0");
    feqAtomsG2800.push("lrs+1002_8:1_sil=16000:plsq=on:sos=on:urr=on:plsql=on:st=1.2:i=228:sd=2:ss=axioms_0");
    feqAtomsG2800.push("lrs+10_8:1_to=lpo:drc=encompass:sil=4000:sos=on:urr=on:newcnf=on:i=1008:sd=2:nm=2:ss=axioms:sgt=32:sup=off:bd=off_0");
    feqAtomsG2800.push("dis-1002_1:64_sil=2000:sos=on:nwc=10.0:i=231:nm=2:ss=axioms:ep=RST:sd=1_0");
    feqAtomsG2800.push("lrs-1010_1:1_to=lpo:sil=2000:sp=reverse_arity:sos=on:urr=ec_only:i=501:sd=2:bd=off:ss=axioms:sgt=16_0");
    feqAtomsG2800.push("dis-1011_100103:1048576_bsr=on:drc=encompass:sil=2000:tgt=full:bsd=on:ile=on:sp=const_min:rnwc=on:nwc=23.5528:s2agt=30:avsqc=2:avsq=on:s2a=on:i=411:s2at=6:avsqr=111405,262144:bsdmm=3:nm=40:uhcvi=on:afr=on:ss=axioms:sgt=5:rawr=on:add=large_0");
    feqAtomsG2800.push("dis+1011_3:8_bsr=unit_only:slsqr=1,16:sil=2000:plsq=on:plsqr=296,127:sp=reverse_frequency:lsd=5:nwc=10.0:slsqc=3:slsq=on:st=3.0:i=412:s2at=4.5:sd=4:slsql=off:nm=16:ins=5:ss=axioms:sgt=20:rawr=on:urr=ec_only:to=lpo_0");
    feqAtomsG2800.push("lrs+1002_1:16_sil=4000:sos=on:sac=on:i=886:bs=unit_only:gsp=on:ss=included:sgt=16:fsr=off:sfv=off:bd=off_0");
    feqAtomsG2800.push("dis+1011_3:1_sil=2000:lsd=10:sac=on:s2a=on:i=258:fsr=off:fd=off:ss=axioms:sd=2:sgt=16_0");
    feqAtomsG2800.push("lrs+21_1:1024_sil=2000:sp=frequency:spb=non_intro:st=3.5:i=420:sd=3:kws=precedence:bd=off:av=off:ss=axioms:sup=off:lcm=predicate_0");
    feqAtomsG2800.push("lrs-1011_1:1_sil=16000:urr=ec_only:flr=on:i=262:ep=RST:ss=axioms:sd=1:lsd=50_0");
    feqAtomsG2800.push("lrs+1002_1:1_to=lpo:sil=4000:sos=on:i=425:sd=1:ss=included_0");
    feqAtomsG2800.push("lrs+1011_1:64_slsqr=117407,1048576:drc=encompass:sil=2000:plsqc=1:plsq=on:plsqr=32300765,1048576:urr=ec_only:rp=on:slsqc=3:slsq=on:i=619:slsql=off:bd=off:rawr=on:fsr=off:br=off:s2at=2.0_0");
    feqAtomsG2800.push("lrs+2_1:1_sil=2000:tgt=ground:sos=on:i=274:sd=1:ss=included:to=lpo:plsq=on:plsqr=32,1_0");
    feqAtomsG2800.push("lrs-1011_1:1_bsr=unit_only:sil=2000:sp=occurrence:sac=on:i=280:sd=3:ss=axioms:sgt=30:newcnf=on_0");
    feqAtomsG2800.push("lrs+1010_1:2_sil=4000:tgt=ground:nwc=10.0:st=2.0:i=280:sd=1:bd=off:ss=axioms_0");
    feqAtomsG2800.push("dis+1011_1:1_sil=2000:urr=ec_only:br=off:st=1.5:i=497:fsr=off:fsd=on:ss=axioms:slsq=on:slsql=off:slsqr=1,16:sup=off_0");
    feqAtomsG2800.push("ott+1002_2835555:1048576_to=lpo:sil=2000:sos=on:fs=off:nwc=10.3801:avsqc=3:updr=off:avsq=on:st=2:s2a=on:i=321:s2at=3:afp=10000:aac=none:avsqr=13357983,1048576:awrs=converge:awrsf=460:bd=off:nm=13:ins=2:fsr=off:amm=sco:afq=1.16719:ss=axioms:rawr=on:fd=off_0");
    feqAtomsG2800.push("lrs-10_1:1_to=lpo:drc=off:sil=8000:sos=on:i=550:ss=axioms:sd=1_0");
    feqAtomsG2800.push("lrs-1002_3:2_sil=2000:sos=on:fd=off:nwc=10.0:flr=on:i=554:nm=16:fsr=off:sup=off:ss=axioms:fs=off:bd=off:fde=none:erd=off_0");
    feqAtomsG2800.push("lrs+2_5:1_to=lpo:sil=2000:plsqc=1:plsq=on:plsqr=32,1:sp=occurrence:sos=all:lma=on:i=337:gsp=on:ss=axioms:rawr=on:sup=off:s2a=on:s2at=3.0_0");
    feqAtomsG2800.push("lrs+11_1:8_sil=2000:fde=unused:sos=all:spb=goal_then_units:lsd=100:i=341:kws=precedence:aac=none:sfv=off_0");
    feqAtomsG2800.push("dis+1002_1:28_sil=64000:sos=on:s2agt=8:sac=on:i=3780:s2a=on:s2at=2.5:ep=RSTC_0");
    feqAtomsG2800.push("dis+1011_1:4_sil=8000:tgt=full:st=1.5:s2a=on:i=2134:s2at=1.2:sd=5:ss=axioms:ep=RS:av=off_0");
    feqAtomsG2800.push("lrs-1002_1:1_anc=all:sil=64000:tgt=full:sos=on:st=1.5:i=371:sd=2:kws=inv_frequency:aac=none:fsr=off:ss=axioms:abs=on:fs=off_0");
    feqAtomsG2800.push("dis+33_1:1_to=lpo:sil=16000:plsq=on:nwc=3.0:s2agt=16:s2a=on:i=3658:s2at=5.5:nm=2:av=off:fsr=off:s2pl=no:ep=RS:erd=off_0");
    feqAtomsG2800.push("dis+1010_2:13_bsr=on:drc=off:sil=32000:fde=none:sos=on:nwc=10.0:sac=on:newcnf=on:s2a=on:i=663:s2at=1.5:awrs=decay:awrsf=8:nm=16:rawr=on:rnwc=on:kws=arity_squared:amm=sco:alpa=random_0");
    feqAtomsG2800.push("lrs+1011_5:1_drc=encompass:sil=2000:urr=on:fd=preordered:i=2101:kws=inv_frequency:s2a=on:s2at=-1.0_0");
    feqAtomsG2800.push("dis+1002_1:1_sil=16000:tgt=ground:sac=on:i=714:sd=2:aac=none:ss=axioms:nwc=10.0_0");
    feqAtomsG2800.push("lrs+1011_4345945:1048576_bsr=unit_only:sil=8000:tgt=full:irw=on:fde=none:sos=on:lma=on:spb=intro:abs=on:urr=on:br=off:fd=preordered:rp=on:nwc=14.3155:s2agt=50:alpa=random:kmz=on:updr=off:s2a=on:i=423:add=off:bs=on:kws=inv_arity_squared:afp=100000:aac=none:awrs=decay:awrsf=1366:nm=2:ins=2:afq=4.07453:uhcvi=on:afr=on:rawr=on:sp=unary_first:bd=off:fsd=on:fsdmm=1:s2at=5.0:sup=off_0");
    feqAtomsG2800.push("lrs+1010_1:28_sil=2000:s2agt=16:st=3.0:s2a=on:i=427:sd=3:ss=axioms:av=off:slsq=on_0");
    feqAtomsG2800.push("lrs+11_2:1_to=lpo:sil=2000:tgt=ground:sp=const_frequency:i=456:bd=off:fsr=off:ss=axioms:av=off:s2a=on:s2at=-1.0_0");
    feqAtomsG2800.push("dis+1011_2:1_sil=2000:fde=unused:plsqc=1:plsq=on:plsqr=36971,524288:nwc=5.0:i=479:ep=RS:nm=7_0");
    feqAtomsG2800.push("dis+1011_1:1_drc=off:sil=2000:fde=unused:sp=const_min:spb=goal_then_units:lsd=20:s2agt=10:newcnf=on:s2a=on:i=869:nm=2:av=off:rawr=on:fsd=on_0");
    feqAtomsG2800.push("dis+11_1:1024_to=lpo:sil=16000:sp=reverse_arity:sos=all:st=1.5:i=511:bd=off:av=off:ss=axioms:sfv=off:sd=4:fd=off_0");
    feqAtomsG2800.push("ott-1010_1915907:1048576_to=lpo:sil=2000:plsq=on:ile=on:plsqr=319573,262144:sp=reverse_arity:sos=on:nwc=6.38626:s2agt=10:avsq=on:s2a=on:i=511:s2at=5.5:sd=1:afp=40000:avsqr=5709,524288:nm=9:ins=2:fsr=off:afq=1.49663:ss=included:rawr=on:acc=model:ccuc=small_ones:fs=off:spb=goal_0");
    feqAtomsG2800.push("lrs+1011_1:8_to=lpo:sil=2000:sos=all:urr=ec_only:br=off:nwc=10.0:newcnf=on:st=3.0:i=548:sd=3:bd=off:nm=2:fdi=50:ss=axioms:sfv=off:sac=on_0");
    feqAtomsG2800.push("lrs+1010_174643:1048576_anc=none:drc=off:sil=2000:tgt=full:sims=off:sp=frequency:lma=on:urr=on:nwc=0.442624:alpa=random:nicw=on:st=3:i=565:sd=4:awrs=decay:awrsf=1057:bd=off:nm=6:ins=1:ss=axioms:sgt=10:rawr=on:afp=2000:afq=1.0096899854800578:br=off_0");
    feqAtomsG2800.push("dis+21_16:1_to=lpo:sil=2000:sp=frequency:urr=on:nwc=10.0:s2a=on:i=585:sd=1:nm=6:ss=included:fsr=off:gsp=on_0");
    feqAtomsG2800.push("lrs-1010_1:128_tgt=ground:si=on:plsq=on:plsqr=2087559,524288:sos=on:st=1.5:i=590:sd=2:rtra=on:ss=included:sil=128000:ins=1:gsp=on:anc=all_dependent_0");
    feqAtomsG2800.push("lrs+1002_1:1_sil=4000:plsq=on:sos=on:plsql=on:i=1095:ss=axioms:sgt=10:avsq=on:avsqr=1,16:ep=RS_0");
    feqAtomsG2800.push("dis+1011_1869663:524288_anc=none:to=lpo:sil=2000:tgt=full:ile=on:sp=weighted_frequency:spb=goal:lsd=20:nwc=21.2407:i=600:sd=1:bd=preordered:nm=4:ins=1:uhcvi=on:gsp=on:ss=axioms_0");
    feqAtomsG2800.push("lrs-1010_1:1024_anc=all_dependent:to=lpo:sp=const_frequency:sos=on:br=off:nwc=10.0:i=618:nm=30:newcnf=on:sil=8000:bd=off:fde=unused:ss=axioms_0");
    feqAtomsG2800.push("lrs+1011_1:1_sil=16000:sos=all:i=619:sd=2:kws=frequency:bd=off:nm=2:ss=axioms:sup=off_0");
    feqAtomsG2800.push("lrs+11_1:1_sos=on:urr=on:s2a=on:i=2202:sd=1:aac=none:ss=axioms:gsp=on:sil=128000:nm=3:bce=on:fd=preordered:alpa=true:etr=on:bd=off:lcm=predicate_0");
    feqAtomsG2800.push("dis+1011_5:1_sil=2000:tgt=full:plsqc=1:plsq=on:plsqr=133465761,1048576:spb=non_intro:i=630:nm=2:ins=1:ss=axioms:rawr=on:alpa=true:kws=precedence:fsr=off_0");
    feqAtomsG2800.push("dis-1011_113:472_sil=256000:nwc=10.0:i=1693:kws=precedence:awrs=decay:bd=off:ss=axioms:rawr=on:plsq=on:plsqr=73,255:amm=sco:ins=1:fsr=off:erd=off:sp=occurrence:fde=unused:lsd=60_0");
    feqAtomsG2800.push("lrs+1002_1:7_drc=encompass:sil=64000:sos=on:urr=full:i=643:sd=2:ss=axioms:sgt=100_0");
    feqAtomsG2800.push("lrs+1011_1:16_sil=2000:plsq=on:plsqr=1,15:urr=on:slsqc=1:slsq=on:st=6.0:i=1250:sd=3:fsr=off:ss=included:rawr=on:sup=off:bd=off_0");
    feqAtomsG2800.push("lrs+1011_1:1_sil=16000:sos=on:i=1322:sd=2:ss=axioms:sgt=16_0");
    feqAtomsG2800.push("lrs+11_1:1_drc=off:sil=4000:fde=unused:sp=unary_frequency:sos=on:fs=off:nwc=17.7715:flr=on:avsq=on:i=736:kws=precedence:avsqr=18,127:bd=off:nm=16:fsr=off:uhcvi=on:rawr=on:s2pl=no:s2agt=8:ss=axioms:sd=1:st=3.5:aac=none:afp=50:afq=2.0_0");
    feqAtomsG2800.push("lrs-1011_1:8_sil=2000:nwc=5.0:flr=on:i=737:nm=2:sup=off:fde=unused:fsr=off:bd=off_0");
    feqAtomsG2800.push("lrs+21_1:1_sil=4000:sos=on:flr=on:i=1407:sd=1:bd=off:nm=2:ss=included:sup=off:fs=off:fsr=off_0");
    feqAtomsG2800.push("lrs+21_1:64_drc=encompass:sil=32000:bsd=on:lma=on:spb=goal:nwc=10.0:i=779:add=large:ss=axioms:sgt=16:irw=on_0");
    feqAtomsG2800.push("lrs-1011_35909:1048576_drc=encompass:sil=2000:tgt=ground:sp=weighted_frequency:spb=goal:fd=preordered:nwc=0.953927:flr=on:s2a=on:i=779:s2at=3:kws=precedence:awrs=decay:awrsf=875:bd=off:nm=3:ins=14:uhcvi=on:rawr=on:s2pl=no:lwlo=on:av=off:fsr=off_0");
    feqAtomsG2800.push("lrs+32_1:1_to=lpo:sil=8000:sp=const_frequency:sos=on:fs=off:fd=off:i=1461:sd=1:bd=off:nm=2:fsr=off:ss=included_0");
    feqAtomsG2800.push("ott+1010_1_aac=none:bce=on:ep=RS:fsd=off:nm=4:nwc=2.0:nicw=on:sas=z3:sims=off:i=1557_0");
    feqAtomsG2800.push("lrs+1010_1:128_sil=8000:sos=all:urr=full:sac=on:i=863:fsd=on:sup=off:ss=included:st=2.5:sd=7_0");
    feqAtomsG2800.push("lrs+11_1:128_slsqr=1,16:sil=64000:slsq=on:st=2.5:i=7137:sd=7:nm=3:av=off:ss=axioms:bd=off_0");
    feqAtomsG2800.push("dis-1010_1:12_sil=64000:tgt=ground:sp=const_max:bce=on:s2agt=100:cond=on:s2a=on:i=1872:s2at=1.5:nm=16:av=off:awrs=converge:awrsf=462:newcnf=on:br=off:bd=off:rawr=on:plsq=on:plsqr=34203,524288:spb=units_0");
    feqAtomsG2800.push("lrs+11_1:16_sil=8000:plsq=on:plsqr=1,32:spb=goal:st=2.0:i=1087:bd=off:ss=axioms:av=off:sd=15:sup=off_0");
    feqAtomsG2800.push("dis+21_1:6_sil=256000:i=1099:ss=included:sd=5:st=2.0:sp=unary_first:sgt=5:newcnf=on:kws=precedence:spb=non_intro:av=off:fd=off_0");
    feqAtomsG2800.push("lrs+1011_6:11_bsr=on:slsqr=4477783,262144:sil=8000:tgt=ground:rp=on:nwc=1.2:slsqc=3:newcnf=on:slsq=on:s2a=on:i=2416:s2at=4.0:sd=5:slsql=off:nm=2:amm=off:ss=axioms:sgt=20:bd=off:updr=off_0");
    feqAtomsG2800.push("lrs+4_1:35_sil=8000:sp=frequency:acc=on:rp=on:s2a=on:i=1331:nm=0:afr=on:aac=none_0");
    feqAtomsG2800.push("lrs+10_1:1_sil=32000:sos=on:i=1340:sd=1:bd=off:ss=included:urr=on:sup=off_0");
    feqAtomsG2800.push("lrs+1011_12:7_drc=off:tgt=ground:sp=frequency:spb=goal:fd=preordered:rp=on:nwc=10.0:newcnf=on:cond=fast:i=1429:kws=precedence:afp=50:afq=4.10402:rawr=on:ss=axioms:sd=2:sgt=50:st=3.5:add=off:ins=11:rnwc=on:sims=off:sil=256000_0");
    feqAtomsG2800.push("dis+1_1:64_sil=16000:sp=reverse_frequency:fd=off:nwc=5.0:sac=on:newcnf=on:i=2895:ss=included:sd=7:st=4.0:fsr=off_0");
    feqAtomsG2800.push("lrs-11_1:1_sil=8000:sos=on:st=2.0:i=1599:sd=2:nm=4:ss=axioms:ep=R_0");
    feqAtomsG2800.push("lrs+2_1:1_sil=256000:plsq=on:plsqr=17685,131072:sos=on:lcm=reverse:i=3156:av=off:ss=axioms:ep=RST:sd=2_0");
    feqAtomsG2800.push("lrs+10_8:1_drc=encompass:sil=256000:sp=reverse_frequency:i=1631:bs=unit_only:aac=none:nm=6:ss=axioms:sup=off:sos=on:acc=model:afp=50_0");
    feqAtomsG2800.push("dis+22_1:1024_sil=8000:plsq=on:plsqr=1,32:fd=off:nwc=2.1:i=3201:av=off:ss=axioms:sgt=16:s2pl=on:sup=off_0");
    feqAtomsG2800.push("lrs+1011_2:3_sil=16000:sos=on:rp=on:newcnf=on:lwlo=on:st=1.5:i=3447:sd=2:bd=off:nm=2:fsr=off:gsp=on:ss=axioms:bce=on:anc=all:sac=on_0");
    feqAtomsG2800.push("lrs+10_1:1_sil=8000:fde=none:sos=on:nwc=10.0:i=1793:ep=RST:av=off:erd=off_0");
    feqAtomsG2800.push("dis-1011_3:2_sil=8000:flr=on:i=1812:av=off:fsr=off:kws=arity_squared_0");
    feqAtomsG2800.push("dis+1010_1:8_sil=16000:plsq=on:plsqr=4,1:s2a=on:i=10544:bd=off:sac=on_0");
    feqAtomsG2800.push("lrs-10_1:1_sil=16000:sos=on:st=3.0:i=2021:sd=2:ep=RST:fsr=off:ss=axioms_0");
    feqAtomsG2800.push("lrs-1010_1:1_drc=off:sil=16000:sos=on:flr=on:i=4790:bd=off:nm=6:ss=included:alpa=false:fs=off:fsr=off_0");
    feqAtomsG2800.push("lrs+1002_1:16_to=lpo:sil=32000:sp=unary_frequency:sos=on:i=2592:bd=off:ss=axioms_0");
    feqAtomsG2800.push("dis+11_1:64_bsr=on:sil=16000:fde=none:sos=all:lsd=10:st=5.5:i=2958:sd=4:av=off:sup=off:gsp=on:ss=axioms:cond=on:bce=on:plsq=on:plsqr=33373429,524288_0");
    feqAtomsG2800.push("dis+1011_1:1_sil=16000:nwc=10.0:sac=on:i=5826:newcnf=on:fdi=20_0");
    feqAtomsG2800.push("dis+1002_1:1_tgt=full:sos=on:rp=on:sac=on:i=3619:ss=axioms:sd=3:cond=fast:add=off:abs=on:fde=none:sil=256000_0");
    feqAtomsG2800.push("lrs-31_1:1_drc=off:sil=4000:tgt=full:fd=preordered:nwc=5.0:lwlo=on:i=3633:ins=5:sac=on:bd=off:lcm=predicate_0");
    feqAtomsG2800.push("dis+1002_25:43_bsr=unit_only:slsqr=1,2:sil=32000:tgt=full:plsq=on:plsqr=93,203:sp=const_min:sos=on:plsql=on:nwc=5.0:alpa=random:newcnf=on:slsq=on:nicw=on:i=3750:add=off:bs=on:slsql=off:fsr=off:uhcvi=on:acc=on_0");
    feqAtomsG2800.push("lrs+1011_4:1_to=lpo:sil=16000:fde=none:plsq=on:plsqr=1,8:sp=occurrence:st=2.0:i=3957:sd=3:ss=axioms:er=known:av=off:awrs=converge:awrsf=500:fsr=off_0");
    feqAtomsG2800.push("ott+10_2651049:1048576_drc=encompass:sil=8000:sp=const_min:sos=on:erd=off:spb=goal_then_units:acc=on:urr=on:rp=on:nwc=3.5019:nicw=on:st=1.5:i=4059:sd=2:kws=inv_frequency:afp=1000000:bd=off:nm=4:afq=2.89144:uhcvi=on:ss=axioms:rawr=on:sup=off_0");
    feqAtomsG2800.push("dis-1002_1:1_sil=8000:sos=on:st=1.2:i=4457:ss=axioms:bd=off:sup=off:fsr=off:sd=5_0");
    feqAtomsG2800.push("lrs+11_1:8_sp=reverse_arity:st=2.0:i=4587:ss=axioms:sil=256000:lcm=predicate:sd=10:av=off_0");
    feqAtomsG2800.push("dis+22_1:8_sil=128000:abs=on:alpa=true:sac=on:i=6044:nm=2:amm=off:sup=off_0");
    feqAtomsG2800.push("dis+11_6:5_sil=8000:plsqc=1:plsq=on:plsqr=2561,256:sp=occurrence:erd=off:urr=on:nwc=10.0:cond=on:s2a=on:i=6488:s2at=6.0:kws=inv_arity_squared:nm=9:av=off:rawr=on:lsd=100:ss=axioms:st=4.0:ep=R:sd=5_0");
    feqAtomsG2800.push("dis+21_16:1_sil=128000:newcnf=on:i=8195:kws=inv_frequency:nm=2:bd=preordered:flr=on:sac=on:ins=1_0");
    feqAtomsG2800.push("lrs-1011_6:1_sos=all:s2a=on:i=9398:sd=2:ss=included:bd=off:sil=128000:fde=none:abs=on:amm=off:gsp=on:sp=const_min:cond=fast:avsq=on:avsqc=1:avsqr=11,2:nm=5:sfv=off:plsq=on:plsqr=199691,1048576_0");
    feqAtomsG2800.push("lrs+11_1:128_st=3.0:i=11271:ss=axioms:av=off:bd=off:to=lpo:sil=256000:nwc=5.0:newcnf=on:fsr=off_0");
    feqAtomsG2800.push("dis+1010_5:1_sil=64000:sp=const_min:sos=on:acc=model:i=11437:kws=precedence:bd=off:nm=20:alpa=random:ss=axioms_0");
    feqAtomsG2800.push("dis+10_71833:524288_drc=off:sil=256000:tgt=ground:nwc=10.0:i=12768:kws=inv_frequency:awrs=decay:nm=78:abs=on:flr=on:slsq=on:slsqc=3:slsqr=4,1:s2at=4.0_0");
    feqAtomsG2800.push("lrs+11_1:128_st=2.0:i=276692:ss=axioms:to=lpo:sil=256000:sd=15:ep=RS_0");
    feqAtomsG2800.push("dis+1010_1:1_av=off:newcnf=on:si=on:rawr=on:rtra=on:i=21387_0");
    feqAtomsG2800.push("dis-1010_1:1_slsqr=3,4:sil=64000:tgt=full:fde=unused:slsqc=1:slsq=on:i=46074:sd=1:ss=included:fsr=off:plsq=on:plsqc=1:plsqr=32,1_0");
    feqAtomsG2800.push("lrs+11_1:1024_sil=128000:plsqc=2:bsd=on:plsq=on:plsqr=5714633,65536:sp=frequency:spb=units:bce=on:rp=on:newcnf=on:i=61101:afp=1000:afq=4.53413:rawr=on:afr=on:uhcvi=on_0");
    feqAtomsG2800.push("dis+1011_4_add=large:amm=off:sims=off:sac=on:sp=frequency:tgt=ground:i=61108_0");

    feqAtomsG2800.push("lrs-1010_54669:524288_sp=const_frequency:sac=on:cond=fast:i=98291:afp=300:aac=none:bd=off:sims=off:aer=off:flr=on:tgt=ground:sil=256000:sfv=off:kws=precedence:alpa=random:spb=intro:s2a=on:s2agt=50:s2at=5.0:updr=off_0");

    // total_instr 1380668
    // len(covered) 466

    Schedule feqAtomsG180;

    feqAtomsG180.push("lrs+1011_1:12_anc=none:drc=off:sil=64000:sims=off:sp=unary_first:spb=goal_then_units:lsd=20:rnwc=on:nwc=2.0:i=53554:add=off:awrs=converge:bd=off:uhcvi=on:tgt=ground:afp=300:afq=1.63_0");
    feqAtomsG180.push("dis+11_1:1_nwc=5.0:s2a=on:i=66616:s2at=3.0:sil=128000:bd=off_0");
    feqAtomsG180.push("lrs+1010_2201:262144_anc=all:drc=encompass:sil=256000:sims=off:sp=frequency:spb=goal_then_units:rp=on:lwlo=on:st=3.0:i=179501:bs=unit_only:nm=6:ins=2:fsd=on:ss=axioms:sgt=16:afr=on:tgt=ground:awrs=decay:awrsf=200:acc=on:ccuc=first_0");
    feqAtomsG180.push("lrs+10_1:3_drc=off:sil=256000:sp=unary_first:lwlo=on:i=216875:kws=precedence:ins=3:rawr=on:nwc=10.0_0");

    feqAtomsG180.push("dis+1011_3:1_sil=256000:tgt=ground:sac=on:i=109:sd=1:ss=included_0");
    feqAtomsG180.push("dis+1010_1:1_sil=2000:nwc=3.0:s2a=on:i=132:ins=5:fsr=off:ss=axioms:sd=2:fd=off_0");
    feqAtomsG180.push("dis+1010_159245:1048576_to=lpo:sil=2000:etr=on:sp=unary_frequency:spb=goal:rnwc=on:nwc=10.9066:st=2:i=124:sd=1:nm=3:av=off:ss=axioms:rawr=on:drc=encompass:foolp=on:sgt=5:cond=fast:er=filter:erape=on:erml=2:s2a=on_0");
    feqAtomsG180.push("lrs+1011_1:1_sil=16000:sos=on:erd=off:i=126:nm=2:ep=RST_0");
    feqAtomsG180.push("lrs+1011_1:1_sil=8000:sp=occurrence:nwc=10.0:st=1.5:i=145:ss=axioms:sgt=4_0");
    feqAtomsG180.push("ott+1002_2835555:1048576_to=lpo:sil=2000:sos=on:fs=off:nwc=10.3801:avsqc=3:updr=off:avsq=on:st=2:s2a=on:i=173:s2at=3:afp=10000:aac=none:avsqr=13357983,1048576:awrs=converge:awrsf=460:bd=off:nm=13:ins=2:fsr=off:amm=sco:afq=1.16719:ss=axioms:rawr=on:fd=off_0");
    feqAtomsG180.push("lrs+2_3:1_to=lpo:sil=256000:irw=on:fde=unused:sp=unary_first:bce=on:nwc=6.0:s2agt=30:newcnf=on:s2a=on:i=226:nm=2_0");
    feqAtomsG180.push("dis+1011_1:1_sil=16000:nwc=7.0:s2agt=64:s2a=on:i=247:ss=axioms:sgt=8:lsd=50:sd=7_0");
    feqAtomsG180.push("lrs+2_1:1_sil=2000:sos=on:urr=on:i=230:kws=inv_frequency:ss=axioms:sd=3:avsq=on:br=off_0");
    feqAtomsG180.push("dis-1010_76381:524288_drc=off:sil=4000:irw=on:sp=frequency:lma=on:spb=goal:rnwc=on:gs=on:nwc=13.9901:s2agt=10:kmz=on:updr=off:sac=on:newcnf=on:gsem=on:cond=fast:s2a=on:i=231:s2at=6:kws=inv_frequency:awrs=converge:awrsf=968:bd=off:nm=10:rawr=on:sfv=off:alpa=random_0");
    feqAtomsG180.push("lrs+1011_1:1_sil=8000:nicw=on:i=532:sd=1:ss=axioms:sgt=64_0");
    feqAtomsG180.push("dis-1010_1:2_bsr=unit_only:sil=32000:tgt=full:i=1280:nm=16:bd=off_0");
    feqAtomsG180.push("dis+1011_1:16_sil=2000:plsq=on:sos=on:st=3.0:i=134:sd=1:av=off:ss=axioms:lsd=10:plsql=on_0");
    feqAtomsG180.push("dis-1010_8:1_sil=64000:sp=occurrence:sos=on:st=2.0:i=135:sd=3:bd=off:ss=axioms:acc=model:to=lpo:sup=off:fs=off:fsr=off:sgt=32_0");
    feqAtomsG180.push("lrs+21_1:16_sil=2000:sp=occurrence:urr=on:flr=on:i=139:sd=1:nm=0:ins=3:ss=included:rawr=on:br=off_0");
    feqAtomsG180.push("ott+1011_1:3_drc=encompass:sil=256000:bsd=on:sp=occurrence:sos=on:newcnf=on:i=160:afp=1:aac=none:amm=off:afq=3.64962_0");
    feqAtomsG180.push("dis-1002_1:1_to=lpo:drc=encompass:sil=2000:sp=const_max:nwc=10.0:s2a=on:i=194:s2at=2.0:afp=10:ins=16:afq=1.4:aac=none:rawr=on:fsr=off:alpa=true_0");
    feqAtomsG180.push("lrs-1010_529157:524288_drc=off:sil=4000:fde=none:sp=occurrence:sos=on:lma=on:abs=on:rnwc=on:nwc=23.317:i=385:sd=12:bd=off:nm=27:ins=3:amm=off:ss=axioms:nicw=on_0");
    feqAtomsG180.push("dis+1011_11:1_sil=2000:avsq=on:i=293:avsqr=1,16:ep=RS:rawr=on:aac=none:lsd=100:mep=off:fde=none:newcnf=on:bsr=unit_only_0");
    feqAtomsG180.push("lrs+11_1:1_sos=on:urr=on:s2a=on:i=178:sd=1:aac=none:ss=axioms:gsp=on:sil=128000:nm=3:bce=on:fd=preordered:alpa=true:etr=on:bd=off:lcm=predicate_0");
    feqAtomsG180.push("lrs+11_1:32_sil=2000:sp=occurrence:lsd=20:rp=on:i=163:sd=1:nm=0:av=off:ss=included:nwc=10.0:flr=on_0");
    feqAtomsG180.push("lrs+1011_4:1_to=lpo:drc=off:sil=8000:sp=frequency:abs=on:urr=on:lsd=10:nwc=5.0:s2agt=4:newcnf=on:st=5.0:s2a=on:i=674:ss=axioms:aac=none:br=off:bd=preordered_0");
    feqAtomsG180.push("dis-1011_1:1024_sil=2000:fde=unused:sos=on:nwc=10.0:i=152:uhcvi=on:ss=axioms:ep=RS:av=off:sp=occurrence:fsr=off:awrs=decay:awrsf=200_0");
    feqAtomsG180.push("lrs+2_2742125:1048576_drc=encompass:sil=2000:sp=const_min:sos=on:lcm=reverse:fd=preordered:nwc=16.4028:newcnf=on:i=172:sd=2:kws=precedence:bd=off:uhcvi=on:ss=axioms:rawr=on:awrs=converge:awrsf=493:cond=fast:tgt=full_0");
    feqAtomsG180.push("lrs+1002_1:128_to=lpo:sil=2000:plsq=on:plsqr=7,2:sos=on:spb=units:fd=preordered:nwc=5.0:i=176:bd=off:nm=4:av=off:rawr=on:newcnf=on:fs=off:fsr=off_0");
    feqAtomsG180.push("dis+1011_2:3_sil=8000:tgt=ground:fde=none:spb=goal_then_units:acc=on:nwc=4.0:updr=off:i=813:kws=inv_frequency:nm=16:ins=3:rawr=on:amm=sco_0");
    feqAtomsG180.push("lrs+1011_2:9_sil=2000:lsd=10:newcnf=on:i=198:sd=2:awrs=decay:ss=included:amm=off:ep=R_0");
    feqAtomsG180.push("dis+2_1:5_to=lpo:drc=off:sil=8000:tgt=full:sp=reverse_frequency:spb=goal_then_units:urr=ec_only:i=154:rawr=on:fsr=off:ss=included_0");
    feqAtomsG180.push("lrs+1011_1:1024_sil=8000:sp=unary_first:nwc=10.0:st=3.0:s2a=on:i=214:s2at=5.0:awrs=converge:awrsf=390:ep=R:av=off:ss=axioms:s2agt=32_0");
    feqAtomsG180.push("lrs+1002_1:8_sil=16000:tgt=ground:fde=none:sp=const_frequency:sos=on:nwc=3.0:i=157_0");
    feqAtomsG180.push("dis+1011_1:1_sil=2000:fd=off:nwc=10.0:s2a=on:i=542:bd=off:nm=2:sup=off:s2at=4.0_0");
    feqAtomsG180.push("dis-1002_3:1_to=lpo:sil=4000:sp=occurrence:fd=off:nwc=6.0:st=2.0:i=162:sd=1:fsr=off:ss=axioms:sgt=16:fs=off_0");
    feqAtomsG180.push("lrs+1002_1:1_sfv=off:drc=encompass:sil=2000:fde=unused:sp=frequency:nwc=10.0:flr=on:st=1.5:i=193:bd=off:nm=0:ins=4:fsr=off:fsd=on:ss=axioms:s2a=on:s2agt=32:to=lpo:aac=none:sims=off_0");
    feqAtomsG180.push("lrs-1002_2:9_anc=none:sil=2000:plsqc=1:plsq=on:avsql=on:plsqr=2859761,1048576:erd=off:rp=on:nwc=21.7107:newcnf=on:avsq=on:i=164:aac=none:avsqr=6317,1048576:ep=RS:fsr=off:rawr=on:afp=50:afq=2.133940627822616:sac=on_0");
    feqAtomsG180.push("dis+1011_1:1024_drc=off:sil=2000:urr=ec_only:br=off:sac=on:i=360:fsr=off_0");
    feqAtomsG180.push("lrs+1011_8157881:1048576_to=lpo:drc=off:sil=2000:fde=unused:sos=on:spb=intro:urr=on:nwc=4.0:i=269:add=off:sd=1:nm=19:fsr=off:uhcvi=on:ss=axioms:sgt=100:ins=3:sup=off:afp=1000:s2pl=no:anc=none:acc=model:fs=off:lma=on_0");
    feqAtomsG180.push("lrs+1010_1:1_to=lpo:sil=2000:plsq=on:plsqr=32,1:sos=on:i=467:sd=2:ss=axioms_0");
    feqAtomsG180.push("dis+1011_1:1_sil=4000:s2agt=4:slsqc=3:slsq=on:i=211:bd=off:av=off:sup=off:ss=axioms:st=3.0_0");
    feqAtomsG180.push("lrs+1_4:1_cond=fast:fde=unused:lcm=predicate:nm=4:s2a=on:sd=3:sos=on:ss=axioms:st=2.0:sil=16000:si=on:rawr=on:rtra=on:i=440_0");
    feqAtomsG180.push("lrs+1011_1:2_drc=encompass:sil=4000:fde=unused:sos=on:sac=on:newcnf=on:i=139:sd=10:bd=off:ins=1:uhcvi=on:ss=axioms:spb=non_intro:st=3.0:erd=off:s2a=on:nwc=3.0_0");
    feqAtomsG180.push("lrs+1011_1:4_sil=2000:tgt=ground:lsd=100:nwc=2.0:st=7.0:i=2264:bd=off:nm=16:av=off:ss=axioms:rawr=on_0");
    feqAtomsG180.push("dis+1011_1:4_sil=4000:i=231:awrs=converge:ep=RS:fsr=off:s2a=on:s2agt=32_0");
    feqAtomsG180.push("dis-1011_4948593:1048576_sfv=off:sil=4000:sp=frequency:sos=on:spb=goal:lsd=1:lcm=predicate:rnwc=on:nwc=16.7798:i=146:sd=2:kws=inv_frequency:awrs=converge:awrsf=336:nm=10:ins=2:av=off:ss=axioms:rawr=on_0");
    feqAtomsG180.push("dis-1002_89073:262144_slsqr=91667,1048576:drc=off:sil=2000:sp=unary_frequency:spb=goal:urr=ec_only:bce=on:lcm=reverse:rp=on:nwc=9.0873:sac=on:slsq=on:nicw=on:cond=fast:i=943:s2at=5.5:kws=precedence:afp=100000:slsql=off:bd=off:nm=5:ins=3:sup=off:afq=1.99538:uhcvi=on:gsp=on:rawr=on:acc=model_0");
    feqAtomsG180.push("lrs+1002_1:1024_drc=encompass:sil=2000:tgt=full:rp=on:i=336:nm=16:ss=axioms:sd=1:st=2.0_0");
    feqAtomsG180.push("lrs+10_8:1_to=lpo:drc=encompass:sil=4000:sos=on:urr=on:newcnf=on:i=149:sd=2:nm=2:ss=axioms:sgt=32:sup=off:bd=off_0");
    feqAtomsG180.push("ott+1011_47:51_anc=all_dependent:slsqr=853,231:sil=4000:sp=reverse_frequency:foolp=on:spb=non_intro:abs=on:s2agt=50:slsqc=1:slsq=on:st=4.0:i=152:s2at=1.5:sd=7:kws=inv_frequency:afp=2000:nm=14:ins=2:afq=1.2:uhcvi=on:afr=on:gsp=on:ss=axioms:sgt=100:rawr=on:tgt=ground:awrs=converge:awrsf=390:bs=unit_only:add=off:flr=on:plsq=on:plsqc=1:plsqr=6705511,1048576:bd=preordered:newcnf=on:nwc=5.0_0");
    feqAtomsG180.push("dis+1011_1:59_slsqr=923,506:to=lpo:drc=encompass:sil=16000:tgt=ground:irw=on:fde=none:spb=goal:bce=on:nwc=5.0:slsqc=1:flr=on:slsq=on:s2a=on:i=206:s2at=6.0:sd=2:afp=1000:ss=axioms:er=filter:rawr=on:fdi=5:rp=on_0");
    feqAtomsG180.push("dis+1010_1178033:262144_sil=2000:ile=on:sp=reverse_frequency:sos=on:erd=off:spb=goal:abs=on:bce=on:lcm=reverse:fd=preordered:nwc=11.49952179089034:kmz=on:i=229:add=large:bs=unit_only:kws=inv_arity:nm=20:amm=off:uhcvi=on:afr=on:rawr=on:fsr=off:bd=off:fde=unused:bsr=unit_only_0");
    feqAtomsG180.push("dis+1011_3:2_drc=encompass:sil=8000:tgt=full:sp=frequency:nwc=10.0:i=831:nm=2:fde=none:ins=1_0");
    feqAtomsG180.push("dis+1010_1:1_sil=4000:sims=off:sp=frequency:nwc=5.0:st=5.0:i=233:av=off:fsr=off:ss=axioms:sd=1:to=lpo:fdi=10_0");
    feqAtomsG180.push("dis+1011_13623:1048576_drc=off:sil=2000:fde=unused:bsd=on:sp=const_min:br=off:fd=preordered:gs=on:nwc=17.1261:gsem=off:i=720:kws=inv_frequency:nm=4:rawr=on:bd=off:fsr=off:bsdmm=1:av=off_0");
    feqAtomsG180.push("lrs+2_1:1_sil=2000:urr=on:flr=on:s2a=on:i=172:s2at=5.0:sd=1:ss=axioms:sgt=8:gsp=on:br=off_0");
    feqAtomsG180.push("dis+1002_1:128_sil=2000:fde=none:i=532:plsq=on:plsqc=1:plsqr=6,1:bd=off:tgt=ground:sac=on:sfv=off:s2a=on:s2at=5.0_0");
    feqAtomsG180.push("lrs+1011_1:1_sil=4000:sos=on:abs=on:fd=preordered:sac=on:st=7.0:i=403:kws=frequency:bd=off:ss=axioms:rawr=on:bs=unit_only:irw=on_0");
    feqAtomsG180.push("lrs+1011_1:128_sil=2000:lsd=10:newcnf=on:i=178:bd=off:fsd=on:ss=axioms:plsq=on:plsqr=9200103,131072:sd=1:lma=on_0");
    feqAtomsG180.push("dis+1011_5:1_sil=2000:fde=unused:nwc=10.0:i=647:ep=R:fs=off:fsr=off:awrs=converge_0");
    feqAtomsG180.push("dis-1002_1:2_sil=2000:slsqc=3:sac=on:slsq=on:i=267:kws=frequency:fsr=off:bd=off:sfv=off_0");
    feqAtomsG180.push("lrs+1011_1:1_to=lpo:drc=off:sil=2000:tgt=full:i=1947:fd=preordered_0");
    feqAtomsG180.push("lrs-1010_1:8_sil=2000:spb=intro:acc=on:rp=on:i=282:sd=1:bd=off:uhcvi=on:ss=axioms:sgt=32:rawr=on:erd=off:alpa=true:anc=none:afp=2000_0");
    feqAtomsG180.push("lrs-1010_1:8_sil=2000:sos=on:i=1837:sd=1:ins=3:ss=included_0");
    feqAtomsG180.push("ott-1010_1032285:1048576_to=lpo:drc=off:sil=2000:tgt=ground:fde=unused:bsd=on:sp=reverse_arity:sos=on:rnwc=on:fd=preordered:nwc=3.32781:s2agt=15:s2a=on:s2pl=on:i=197:s2at=4.5:bs=unit_only:bd=off:nm=14:amm=off:uhcvi=on:rawr=on_0");
    feqAtomsG180.push("dis-1004_1:32_sil=2000:tgt=ground:sos=on:spb=goal_then_units:fd=preordered:gs=on:nwc=12.720749687760888:i=198:gsaa=full_model:ins=1:sac=on:fsr=off:fs=off_0");
    feqAtomsG180.push("lrs-34_1:1_sil=4000:erd=off:urr=on:nwc=3.0:s2agt=16:s2a=on:i=212:br=off:ep=R:ins=1_0");
    feqAtomsG180.push("dis+22_1:32_sil=2000:fde=none:nwc=10.0:slsqc=3:slsq=on:i=213:slsql=off:nm=16:fsr=off:fsd=on:ss=axioms_0");
    feqAtomsG180.push("dis-1003_1:1_drc=off:sil=2000:sos=all:i=329:av=off:irw=on:plsq=on:plsqc=1:plsqr=32,1:sfv=off_0");
    feqAtomsG180.push("dis+1010_1:1_sil=2000:nwc=5.0:i=220:nm=4:av=off:rp=on:ep=R_0");
    feqAtomsG180.push("lrs+1011_1555545:262144_anc=none:bsr=unit_only:sil=2000:ile=on:abs=on:fd=preordered:nwc=20.1634:lwlo=on:avsq=on:cond=fast:st=6:i=223:kws=precedence:avsqr=9293391,524288:nm=23:sup=off:ss=included:rawr=on:lsd=1:bd=preordered:etr=on:afp=100000:afq=2.9510012289029954_0");
    feqAtomsG180.push("lrs+1666_1:1_sil=4000:sp=occurrence:sos=on:urr=on:newcnf=on:i=224:amm=off:ep=R:erd=off:nm=0:plsq=on:plsqr=14,1_0");
    feqAtomsG180.push("dis-1010_1:1_bsr=unit_only:to=lpo:sil=256000:fde=none:plsq=on:plsqr=205,29:sp=occurrence:sos=on:abs=on:newcnf=on:st=6.0:i=227:sd=2:bd=off:amm=off:ss=axioms:rawr=on_0");
    feqAtomsG180.push("dis+1011_1:1_sil=2000:sos=on:lsd=100:rp=on:nwc=10.0:s2agt=16:newcnf=on:i=739:bd=off:fsr=off:rawr=on:avsq=on:avsql=on:avsqr=117,449:s2a=on:bs=on_0");
    feqAtomsG180.push("dis+1011_4:1_sil=2000:nwc=10.0:newcnf=on:i=228:sd=1:nm=2:ss=axioms:fde=unused:sup=off:av=off_0");
    feqAtomsG180.push("lrs-1011_23:2_drc=encompass:fde=unused:plsq=on:urr=on:nwc=10.0:sac=on:s2a=on:i=359:sd=2:ss=axioms:sil=256000:kws=inv_frequency_0");
    feqAtomsG180.push("dis+10_16:63_anc=none:to=lpo:sil=2000:fde=none:sos=on:nwc=10.0:i=236:sd=1:aac=none:ep=RS:fsr=off:ss=axioms:st=5.0_0");
    feqAtomsG180.push("dis-1011_1:32_to=lpo:drc=off:sil=2000:sp=reverse_arity:sos=on:foolp=on:lsd=20:nwc=1.49509792053687:s2agt=30:avsq=on:s2a=on:s2pl=no:i=242:s2at=5.0:avsqr=5593,1048576:nm=0:fsr=off:amm=sco:rawr=on:awrs=converge:awrsf=427:ss=included:sd=1:slsq=on:fd=off_0");
    feqAtomsG180.push("lrs+1011_7141:1048576_sil=2000:plsq=on:plsqr=2328305,1048576:sp=frequency:sos=on:plsql=on:fd=off:nwc=19.7177:cond=fast:st=3:i=531:bd=off:nm=2:ins=2:av=off:uhcvi=on:fdi=16:ss=included:lsd=5_0");
    feqAtomsG180.push("lrs+1002_14319:131072_to=lpo:drc=encompass:sil=2000:tgt=ground:fde=none:sp=const_max:sos=on:spb=units:lcm=predicate:nwc=7.734471748972603:flr=on:newcnf=on:i=247:add=large:awrs=decay:awrsf=1079:bd=off:nm=2:ins=1:fsr=off:uhcvi=on:rawr=on:anc=all_dependent:aac=none:fs=off_0");
    feqAtomsG180.push("lrs+1011_1:1_sil=4000:sos=on:st=3.0:i=406:sd=1:ss=axioms_0");
    feqAtomsG180.push("lrs+11_4:1_sil=2000:tgt=full:sos=on:erd=off:spb=goal_then_units:sac=on:st=6.0:i=257:nm=3:ss=included:sd=1:s2pl=on:awrs=converge:awrsf=20:afp=50:afq=1.2_0");
    feqAtomsG180.push("lrs+10_1:1_sil=16000:sp=frequency:nwc=10.0:s2agt=5:s2a=on:i=259:sd=2:nm=2:ss=axioms:sgt=8:bd=off_0");
    feqAtomsG180.push("lrs+1010_1:7_slsqr=318,127:sil=8000:fde=none:bsd=on:spb=goal:bce=on:gs=on:nwc=4.0:slsqc=2:slsq=on:s2a=on:i=577:nm=3:av=off:fsr=off:rawr=on:bsdmm=2_0");
    feqAtomsG180.push("lrs+1_1:1_sil=4000:plsqc=1:plsq=on:plsqr=108,31:sos=on:st=5.0:i=600:sd=2:bd=off:fsr=off:ss=axioms:rawr=on:bce=on:aac=none:afr=on_0");
    feqAtomsG180.push("lrs+1010_1:1_anc=all_dependent:sil=2000:tgt=ground:nwc=5.0:s2agt=20:alpa=false:newcnf=on:avsq=on:s2a=on:i=271:avsqr=1,16:bd=off:sac=on:aac=none:erd=off_0");
    feqAtomsG180.push("lrs-1002_6:7_sil=4000:sos=on:nwc=10.0:i=273:ep=R:ins=1:fsr=off:gsp=on:fs=off:fde=none:avsq=on:bce=on_0");
    feqAtomsG180.push("lrs+1011_1:1_sil=2000:i=450:ep=RS:nm=32:ss=axioms:sos=on_0");
    feqAtomsG180.push("lrs-1011_3:1_sil=2000:tgt=ground:sos=on:flr=on:i=292:bce=on:kws=inv_frequency_0");
    feqAtomsG180.push("lrs-1011_1:64_slsqr=1674187,131072:sil=4000:plsq=on:lsd=50:plsql=on:slsq=on:i=293:slsql=off:bd=off:nm=3:amm=off:gsp=on:ss=axioms:fsr=off_0");
    feqAtomsG180.push("lrs+1010_1:1_slsqr=430,487:sil=4000:fde=none:plsq=on:plsqr=7,29:erd=off:plsql=on:rp=on:nwc=14.055527276864483:slsqc=3:newcnf=on:slsq=on:i=295:bd=off:av=off:rawr=on_0");
    feqAtomsG180.push("dis+1011_1:4_bsr=on:to=lpo:sil=2000:tgt=ground:plsqc=1:plsq=on:plsqr=4477983,65536:sp=frequency:erd=off:spb=goal:nwc=2.0:sac=on:newcnf=on:cond=fast:st=5.0:i=311:nm=16:ss=axioms:rawr=on:lsd=100:awrs=converge_0");
    feqAtomsG180.push("dis+1011_4:1_slsqr=11827605,262144:sil=2000:sp=const_max:spb=non_intro:acc=on:newcnf=on:slsq=on:nicw=on:i=312:kws=precedence:bd=off:rawr=on:alpa=true:bsd=on:bsr=unit_only:urr=ec_only_0");
    feqAtomsG180.push("dis+4_8:1_sil=2000:rp=on:nwc=10.0:alpa=true:sac=on:s2a=on:i=327:ep=R:ss=axioms:s2pl=on_0");
    feqAtomsG180.push("lrs+10_1:14_bsr=on:sil=2000:sp=occurrence:sos=on:bce=on:gs=on:newcnf=on:nicw=on:i=330:gsaa=from_current:amm=off:rawr=on:avsq=on:avsqr=2,7:fsr=off_0");
    feqAtomsG180.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:si=on:rawr=on:rtra=on:i=1844_0");
    feqAtomsG180.push("lrs+3_1:1024_to=lpo:erd=off:spb=goal:urr=on:cond=fast:i=354:awrs=converge:awrsf=330:av=off:ss=axioms:sgt=16:sup=off:gsp=on:sd=1:sil=32000:nwc=5.0_0");
    feqAtomsG180.push("dis+1011_4:1_sil=2000:fde=unused:lsd=100:nwc=5.0:newcnf=on:i=906:nm=2:ss=axioms_0");
    feqAtomsG180.push("lrs+1011_1:1024_sil=4000:br=off:i=374:bd=off:fd=preordered:slsq=on:slsql=off:slsqc=2:slsqr=1,4:s2at=4.0_0");
    feqAtomsG180.push("lrs+1002_4:3_sil=2000:nwc=5.0:i=1197:sd=2:nm=10:ss=axioms_0");
    feqAtomsG180.push("lrs+33_8:7_anc=all:sil=4000:urr=full:br=off:st=3.0:i=381:sd=2:afp=10:afq=2.0:ss=axioms:rawr=on:fsr=off:gsp=on:nwc=0.9918136297139506_0");
    feqAtomsG180.push("lrs+1010_1:4_sil=2000:tgt=ground:sp=reverse_frequency:nwc=5.0:i=1546:av=off:bd=off:kmz=on_0");
    feqAtomsG180.push("lrs+1002_63:8_sil=4000:sp=frequency:urr=on:lcm=reverse:nwc=10.0:flr=on:i=396:fdi=1:fsr=off:br=off_0");
    feqAtomsG180.push("lrs-21_7:15_sil=32000:sp=unary_first:sos=on:spb=units:urr=ec_only:newcnf=on:i=700:ep=RST:flr=on:gsp=on_0");
    feqAtomsG180.push("lrs+21_1:1_sil=64000:sp=weighted_frequency:s2a=on:i=6386:s2at=4.0:kws=inv_frequency:aac=none:bd=off:bsr=on:amm=off:flr=on:abs=on:sac=on:bs=on_0");
    feqAtomsG180.push("lrs+1011_1:1_sil=16000:fde=unused:plsqc=1:plsq=on:plsqr=32,1:sos=on:nwc=10.0:i=1055:kws=frequency:nm=2:lsd=1:bd=off_0");
    feqAtomsG180.push("lrs+11_1:1_bsr=unit_only:to=lpo:sil=16000:sos=on:spb=goal:urr=on:sac=on:st=2.0:i=421:sd=2:bd=off:nm=6:ss=axioms:bce=on:sup=off:br=off_0");
    feqAtomsG180.push("dis+1011_16:1_anc=all_dependent:sil=4000:tgt=ground:fde=unused:sos=on:acc=model:newcnf=on:avsq=on:i=747:bs=on:avsqr=32,501:uhcvi=on:rawr=on:nwc=10.0:alpa=true:slsq=on:slsqr=5,16_0");
    feqAtomsG180.push("lrs-1011_1:2_nwc=10.0:s2agt=30:s2a=on:i=424:ep=RS:gsp=on:awrs=converge:awrsf=1354:rnwc=on:fsr=off:sil=16000_0");
    feqAtomsG180.push("dis+1_8:1_to=lpo:sil=4000:sos=on:spb=goal_then_units:fd=off:gs=on:newcnf=on:st=5.0:i=431:sd=2:av=off:sup=off:ss=axioms:gsp=on:fde=none:s2a=on:s2agt=8_0");
    feqAtomsG180.push("lrs+1002_1624159:1048576_to=lpo:sil=64000:fde=none:sp=frequency:sos=on:spb=non_intro:nwc=15.7653:s2agt=30:avsqc=2:avsq=on:s2a=on:i=1108:s2at=3:sd=2:avsqr=6990209,1048576:awrs=decay:awrsf=762:bd=off:nm=4:ss=included:fd=off:rawr=on:fs=off:fsr=off:aac=none_0");
    feqAtomsG180.push("lrs-1011_34:69_slsqr=4313211,131072:sil=2000:sp=weighted_frequency:rp=on:nwc=10.0:slsqc=1:slsq=on:i=785:s2at=3.0:slsql=off:bd=off:nm=4:ins=1:rawr=on_0");
    feqAtomsG180.push("lrs-35_1:128_anc=none:bsr=unit_only:fde=unused:sos=all:urr=on:fd=off:nwc=10.0:slsq=on:st=2.0:i=448:bs=unit_only:gsp=on:ss=axioms:sd=1:alpa=true:sil=8000_0");
    feqAtomsG180.push("lrs+11_1:1_sil=8000:abs=on:lsd=10:nwc=10.0:sac=on:i=454:sd=1:bd=off:ss=axioms:newcnf=on:sup=off_0");
    feqAtomsG180.push("dis+1011_5:2_to=lpo:sil=8000:tgt=ground:plsq=on:plsqr=65749,1048576:spb=goal:nwc=10.0:newcnf=on:i=480:rawr=on:av=off:nm=5:awrs=converge:awrsf=340:bsd=on:s2a=on:fdi=1_0");
    feqAtomsG180.push("lrs+2_8:1_drc=encompass:sil=2000:tgt=ground:fde=unused:urr=full:i=861:sup=off:slsq=on:slsql=off:slsqc=1:slsqr=1,2:s2at=5.0:br=off_0");
    feqAtomsG180.push("dis+1011_2:1_sil=2000:fde=unused:plsqc=1:plsq=on:plsqr=36971,524288:nwc=5.0:i=484:ep=RS:nm=7_0");
    feqAtomsG180.push("lrs+1011_9:64_slsqr=1,4:sil=2000:fde=none:nwc=5.0:newcnf=on:slsq=on:i=2129:awrs=converge:awrsf=965:ep=R:av=off_0");
    feqAtomsG180.push("lrs-1011_4:7_sil=2000:tgt=full:bsd=on:spb=goal:nwc=5.0:updr=off:newcnf=on:i=928:kws=arity_squared:rawr=on:bsdmm=2_0");
    feqAtomsG180.push("dis+1002_1:1_sil=2000:tgt=full:spb=goal:avsq=on:i=545:avsqr=19,107:er=known:rawr=on:nwc=3.7:cond=fast:abs=on_0");
    feqAtomsG180.push("lrs-1010_1:1_sil=4000:bsd=on:spb=goal_then_units:s2a=on:i=1465:s2at=2.0:bs=on:sd=4:aac=none:bd=off:nm=16:fsr=off:ss=axioms:sgt=8:kws=precedence:gsp=on_0");
    feqAtomsG180.push("lrs-1011_1:2_to=lpo:sil=8000:fde=unused:rp=on:st=5.0:s2a=on:i=556:ep=R:ss=axioms:flr=on:newcnf=on_0");
    feqAtomsG180.push("dis+21_1:1_to=lpo:sil=4000:plsq=on:sos=on:spb=units:i=574:sd=2:ss=axioms:sgt=8_0");
    feqAtomsG180.push("ott+1010_1_aac=none:bce=on:ep=RS:fsd=off:nm=4:nwc=2.0:nicw=on:sas=z3:sims=off:i=2020_0");
    feqAtomsG180.push("lrs-1002_51:127_bsr=unit_only:sil=16000:tgt=ground:acc=on:sac=on:avsq=on:st=5.0:i=1136:sd=2:avsqr=49633,1048576:ins=2:fsr=off:gsp=on:ss=axioms:rawr=on:awrs=converge:awrsf=220:bce=on:bd=off:fd=off:sfv=off_0");
    feqAtomsG180.push("dis-1011_2:3_slsqr=879,448:irw=on:sp=reverse_frequency:slsqc=2:slsq=on:cond=fast:i=622:s2at=4.0:bs=unit_only:sup=off:ss=axioms:sgt=15:rawr=on:lsd=5:sil=8000:nicw=on_0");
    feqAtomsG180.push("dis+1011_1:9_bsr=unit_only:sil=2000:plsq=on:plsqr=375,251:sp=const_frequency:sos=on:spb=intro:urr=on:flr=on:slsq=on:i=636:av=off:fsr=off:rawr=on:ss=axioms:sd=3:sgt=16:st=3.0:rp=on:to=lpo_0");
    feqAtomsG180.push("ott+10_107421:1048576_to=lpo:drc=off:sil=4000:fde=none:sos=on:lma=on:spb=intro:gs=on:nwc=24.2524:gsem=off:i=664:sd=3:afp=40000:awrs=decay:awrsf=1166:nm=6:afq=1.99252:uhcvi=on:ss=axioms:rawr=on:sp=const_max:add=off_0");
    feqAtomsG180.push("dis-1011_1:12_sil=4000:fde=unused:sp=occurrence:lsd=20:nwc=5.0:s2agt=10:updr=off:cond=fast:s2a=on:i=667:ep=RS:nm=3:ins=1:av=off:rawr=on:s2at=3.0_0");
    feqAtomsG180.push("dis+1011_543:505_drc=encompass:sil=128000:tgt=full:etr=on:sp=frequency:nwc=4.8:avsqc=4:sac=on:avsq=on:st=7.0:i=3665:kws=precedence:avsqr=2669309,1048576:awrs=converge:awrsf=975:bd=off:nm=16:ss=axioms:rawr=on:bsd=on:add=large_0");
    feqAtomsG180.push("lrs-1011_19:210_drc=encompass:sil=16000:sp=weighted_frequency:spb=non_intro:nwc=7.1:cond=fast:st=1.5:s2a=on:i=720:s2at=3.0:add=off:sd=2:kws=precedence:afp=10:bd=off:ins=1:afq=2.810910500672621:ss=axioms:sac=on:plsq=on:plsql=on:plsqr=2,17:plsqc=3_0");
    feqAtomsG180.push("lrs+1011_722839:524288_sil=4000:tgt=ground:fde=none:plsq=on:plsqr=5516061,65536:sp=const_max:spb=goal:acc=on:lsd=5:fd=preordered:nwc=19.5454:avsqc=4:sac=on:newcnf=on:lwlo=on:avsq=on:i=802:afp=1000000:avsqr=2357819,1048576:bd=off:nm=0:afq=4.85051:uhcvi=on:rawr=on:avsql=on_0");
    feqAtomsG180.push("dis+1011_16:1_slsqr=5605329,524288:to=lpo:sil=4000:rp=on:slsqc=1:slsq=on:i=803:bd=off:fsr=off:lsd=50_0");
    feqAtomsG180.push("ott+10_2557:524288_anc=all_dependent:slsqr=1107323,1048576:drc=off:ccuc=first:sil=2000:tgt=ground:plsqc=5:plsq=on:plsqr=554689,1048576:sp=frequency:sos=on:acc=on:urr=on:plsql=on:gs=on:nwc=1.55306:s2agt=30:slsq=on:st=5:i=861:sd=2:awrs=converge:awrsf=1188:bd=off:nm=2:ins=3:fsr=off:fsd=on:ss=axioms:sgt=15:rawr=on:fsdmm=1_0");
    feqAtomsG180.push("dis+1002_8:15_to=lpo:sil=4000:tgt=ground:sp=weighted_frequency:spb=goal_then_units:s2agt=16:nicw=on:st=1.5:s2a=on:i=901:aac=none:nm=32:ss=axioms:sims=off_0");
    feqAtomsG180.push("dis+11_1:5_drc=encompass:sil=4000:sp=frequency:s2a=on:i=923:av=off:fsr=off:lcm=reverse:fde=none_0");
    feqAtomsG180.push("lrs+1011_1:1_sil=2000:sos=on:erd=off:spb=units:st=3.0:i=929:kws=precedence:aac=none:nm=0:ss=axioms_0");
    feqAtomsG180.push("lrs-1011_8:1_bsr=on:sil=4000:tgt=ground:sos=on:lsd=10:newcnf=on:i=948:bd=off:av=off:ss=axioms:rp=on_0");
    feqAtomsG180.push("lrs+3_1:1_sil=2000:plsq=on:plsqr=23463,524288:sos=on:erd=off:urr=on:bce=on:rp=on:st=2.0:i=957:bs=unit_only:sd=2:bd=off:ss=axioms:rawr=on:anc=none:sac=on:slsq=on:bsr=on:lcm=reverse_0");
    feqAtomsG180.push("dis+1011_3:1_anc=all_dependent:bsr=unit_only:drc=encompass:sil=2000:nwc=10.0:alpa=false:sac=on:i=1032:kws=precedence:gsp=on:erd=off:bd=off:afp=50:afq=1.276_0");
    feqAtomsG180.push("lrs-1010_1:16_sfv=off:to=lpo:sil=2000:tgt=full:erd=off:rp=on:nwc=10.0:sac=on:newcnf=on:i=1039:flr=on:bd=off:updr=off_0");
    feqAtomsG180.push("dis+1011_1:8_sil=8000:sos=on:bce=on:rp=on:i=1048:nm=6:av=off_0");
    feqAtomsG180.push("lrs+1010_1:1_to=lpo:sil=2000:sos=on:fd=off:i=1089:bd=off_0");
    feqAtomsG180.push("lrs+1011_4:1_to=lpo:sil=16000:fde=none:plsq=on:plsqr=1,8:sp=occurrence:st=2.0:i=1096:sd=3:ss=axioms:er=known:av=off:awrs=converge:awrsf=500:fsr=off_0");
    feqAtomsG180.push("lrs-1010_1:32_sfv=off:sil=2000:fde=unused:sp=weighted_frequency:flr=on:s2a=on:i=1119:s2at=7.0:bd=off:kws=precedence_0");
    feqAtomsG180.push("lrs-1002_9:13_sil=4000:tgt=ground:etr=on:spb=non_intro:rp=on:newcnf=on:i=1173:add=large:afp=50:bd=off:ins=1:fsr=off:afq=4.13736:gsp=on:ss=axioms:sgt=16:rawr=on:flr=on:bce=on_0");
    feqAtomsG180.push("dis+1011_1:16_sil=2000:urr=ec_only:br=off:i=1186:ss=axioms:st=2.0:fsr=off:drc=encompass:anc=none_0");
    feqAtomsG180.push("lrs+1010_3:1_anc=all_dependent:to=lpo:drc=encompass:sil=4000:plsqc=1:plsq=on:plsqr=5192987,65536:sp=occurrence:sos=on:urr=full:bce=on:rp=on:slsq=on:i=1202:bd=off:rawr=on:uhcvi=on:avsq=on:avsql=on:alpa=false_0");
    feqAtomsG180.push("ott-1010_1915907:1048576_to=lpo:sil=2000:plsq=on:ile=on:plsqr=319573,262144:sp=reverse_arity:sos=on:nwc=6.38626:s2agt=10:avsq=on:s2a=on:i=1208:s2at=5.5:sd=1:afp=40000:avsqr=5709,524288:nm=9:ins=2:fsr=off:afq=1.49663:ss=included:rawr=on:acc=model:ccuc=small_ones:fs=off:spb=goal_0");
    feqAtomsG180.push("lrs+1011_1:1_sil=8000:sp=occurrence:nwc=10.0:i=1212:ss=axioms:sgt=8_0");
    feqAtomsG180.push("lrs+1010_1:1_sil=2000:flr=on:nicw=on:st=2.0:i=1258:sd=2:bd=off:fsr=off:ss=axioms_0");
    feqAtomsG180.push("lrs-1011_1:1_sil=16000:plsq=on:plsqr=10230343,1048576:sos=on:lsd=20:sac=on:s2a=on:i=6152:bd=off:ss=axioms:rawr=on:bce=on_0");
    feqAtomsG180.push("dis+1010_9:61_anc=all:drc=off:sil=16000:tgt=full:urr=ec_only:s2a=on:i=4987:s2at=3.0:nm=0:fsr=off:uhcvi=on:acc=model:aac=none:newcnf=on:bd=off:awrs=converge:awrsf=377:fs=off_0");
    feqAtomsG180.push("dis-1011_1:5_sil=2000:tgt=full:sims=off:gs=on:nwc=5.0:newcnf=on:cond=fast:i=1377:sd=2:uhcvi=on:ss=axioms:sgt=8:rawr=on:gsp=on_0");
    feqAtomsG180.push("lrs+1011_2:3_slsqr=4,1:slsqc=1:slsq=on:i=1391:ep=R:av=off:sil=4000:si=on:rtra=on:updr=off:ins=1:nwc=6.24494712:sp=const_min:mep=off:kws=frequency:fdi=1:rawr=on:lsd=5:slsql=off_0");
    feqAtomsG180.push("dis+1011_1:4_afp=10010:amm=off:anc=none:awrs=decay:awrsf=50:ep=RSTC:fde=unused:lma=on:nm=16:nwc=5.0:s2a=on:sp=frequency:urr=ec_only:si=on:rawr=on:rtra=on:i=1441_0");
    feqAtomsG180.push("lrs-31_1:1_drc=off:sil=4000:tgt=full:fd=preordered:nwc=5.0:lwlo=on:i=1544:ins=5:sac=on:bd=off:lcm=predicate_0");
    feqAtomsG180.push("lrs+1011_1:13_sil=2000:tgt=full:sims=off:sp=occurrence:abs=on:newcnf=on:i=1571:nm=4:ss=axioms:rawr=on:amm=off_0");
    feqAtomsG180.push("lrs+3_1083:1048576_anc=all_dependent:bsr=on:drc=encompass:sil=4000:fde=none:sims=off:plsq=on:plsqr=483329,262144:sp=occurrence:sos=on:lma=on:bce=on:lcm=reverse:fd=preordered:nwc=11.0613:s2agt=15:s2a=on:i=1576:kws=inv_frequency:awrs=decay:awrsf=833:nm=49:amm=sco:uhcvi=on:rawr=on:gs=on_0");
    feqAtomsG180.push("dis+1_1:64_sil=16000:spb=goal_then_units:urr=on:sac=on:st=-1.0:i=15318:bd=off:ss=axioms:fsr=off_0");
    feqAtomsG180.push("lrs-11_4:1_anc=all_dependent:slsqr=1,5:sil=2000:sos=all:spb=goal:br=off:alpa=true:newcnf=on:slsq=on:st=1.5:i=1714:aac=none:nm=16:ins=1:ss=axioms:bs=unit_only:drc=off_0");
    feqAtomsG180.push("lrs-1010_54669:524288_sp=const_frequency:sac=on:cond=fast:i=1773:afp=300:aac=none:bd=off:sims=off:aer=off:flr=on:tgt=ground:sil=256000:sfv=off:kws=precedence:alpa=random:spb=intro:s2a=on:s2agt=50:s2at=5.0:updr=off_0");
    feqAtomsG180.push("lrs-1002_1:1_sil=8000:urr=on:nwc=7.0:i=1782:nm=20:av=off:fsr=off:rp=on:bd=off_0");
    feqAtomsG180.push("dis-1011_3:1_sil=32000:fde=none:sos=all:nwc=5.0:i=3557:ep=R:aac=none_0");
    feqAtomsG180.push("dis+1011_1:1_aac=none:bs=unit_only:ep=RS:gsp=on:nwc=5.0:rnwc=on:s2a=on:s2at=3.0:slsq=on:slsqc=2:slsqr=1,8:si=on:rawr=on:rtra=on:i=2119_0");
    feqAtomsG180.push("dis+1010_111341:524288_bsr=on:drc=encompass:sil=64000:sp=reverse_frequency:spb=units:bce=on:newcnf=on:s2a=on:i=4238:s2at=3.0:bs=on:afp=300:bd=off:afq=1.999_0");
    feqAtomsG180.push("lrs+1010_2:5_anc=all_dependent:to=lpo:sil=32000:tgt=ground:spb=goal:abs=on:sac=on:i=2177:nm=16:amm=sco:fdi=10:avsq=on:avsqc=4_0");
    feqAtomsG180.push("lrs+1010_2:5_bsr=on:to=lpo:sil=64000:bsd=on:sp=frequency:sos=on:urr=ec_only:nwc=4.4:updr=off:newcnf=on:i=2797:ins=2:fsr=off:uhcvi=on:afr=on:rawr=on_0");
    feqAtomsG180.push("lrs+1011_1:2_to=lpo:sil=8000:plsqc=1:plsq=on:plsqr=326,59:sp=weighted_frequency:plsql=on:nwc=10.0:newcnf=on:i=5789:awrs=converge:awrsf=200:bd=off:ins=1:rawr=on:alpa=false:avsq=on:avsqr=1,16_0");
    feqAtomsG180.push("ott+1002_2:5_acc=on:bd=preordered:bsr=on:er=known:flr=on:fsd=off:fde=none:msp=off:nm=64:sos=on:sac=on:sp=reverse_frequency:i=12100_0");
    feqAtomsG180.push("dis+1002_3:2_to=lpo:tgt=full:sp=const_min:spb=non_intro:abs=on:rp=on:nwc=5.0:avsqc=1:avsq=on:i=3115:sd=1:avsqr=4,1:ss=axioms:sgt=20:alpa=true:sil=256000_0");
    feqAtomsG180.push("dis+1011_1:99_anc=none:fde=unused:plsqc=2:bsd=on:plsq=on:plsqr=109,504:sp=reverse_frequency:spb=intro:rp=on:alpa=random:s2a=on:i=3258:s2at=-1.0:aac=none:nm=16:rawr=on:sil=256000:acc=model_0");
    feqAtomsG180.push("dis+1010_1:1_slsqr=11392477,1048576:sil=128000:tgt=full:sims=off:sp=occurrence:nwc=9.0:slsqc=1:slsq=on:i=3273:s2at=5.0:slsql=off:nm=14:uhcvi=on:rawr=on:sac=on:newcnf=on:afp=300:afq=2.16348848191352:plsq=on:plsqc=1:plsqr=17849919,524288:ss=axioms:st=7.0:plsql=on:amm=off:rp=on_0");
    feqAtomsG180.push("lrs+1011_1:1_to=lpo:drc=off:sil=16000:bsd=on:fs=off:lsd=5:nwc=2.0:avsq=on:i=4007:sd=3:afp=1000:avsqr=24555,524288:bd=preordered:nm=16:fsr=off:fsd=on:uhcvi=on:ss=axioms:sgt=15:rawr=on:irw=on:etr=on_0");
    feqAtomsG180.push("lrs-1011_6:1_sos=all:s2a=on:i=4178:sd=2:ss=included:bd=off:sil=128000:fde=none:abs=on:amm=off:gsp=on:sp=const_min:cond=fast:avsq=on:avsqc=1:avsqr=11,2:nm=5:sfv=off:plsq=on:plsqr=199691,1048576_0");
    feqAtomsG180.push("dis-1010_1:1_slsqr=3,4:sil=64000:tgt=full:fde=unused:slsqc=1:slsq=on:i=4226:sd=1:ss=included:fsr=off:plsq=on:plsqc=1:plsqr=32,1_0");
    feqAtomsG180.push("lrs-10_1:3_urr=on:br=off:nwc=1.5:newcnf=on:st=2.0:s2a=on:i=4266:s2at=-1.0:bs=unit_only:sd=2:ss=axioms:sgt=32:sil=32000:gsp=on:bce=on:erd=off_0");
    feqAtomsG180.push("dis-1002_6_acc=on:anc=none:bce=on:cond=fast:drc=off:fsd=off:fde=none:gsp=on:irw=on:sac=on:sp=scramble:tgt=ground:urr=ec_only:si=on:rtra=on:rawr=on:rp=on:i=22087_0");
    feqAtomsG180.push("dis+10_1:1024_sil=16000:fs=off:gs=on:i=4835:ins=1:fsr=off:sac=on_0");
    feqAtomsG180.push("lrs+1011_10574001:1048576_slsqr=8791195,262144:drc=off:sil=8000:tgt=full:fde=unused:etr=on:sp=const_min:foolp=on:spb=goal:urr=ec_only:rp=on:nwc=7.13168:s2agt=10:slsqc=1:updr=off:slsq=on:lwlo=on:i=5190:afp=2000:awrs=converge:slsql=off:awrsf=480:bd=off:nm=12:ins=7:amm=sco:afq=2.46635:rawr=on_0");
    feqAtomsG180.push("lrs+1011_1:64_anc=all:plsq=on:plsqr=32,1:fs=off:sac=on:i=12193:fsr=off:avsq=on:avsqc=1:sil=256000:ins=1_0");
    feqAtomsG180.push("lrs+1011_7:1_bsr=unit_only:drc=off:fde=none:sp=const_min:nwc=10.0:sac=on:i=12220:kws=inv_arity:ss=axioms:rawr=on:urr=ec_only:lsd=10:alpa=false:lwlo=on:sil=256000:nm=20:spb=intro:uhcvi=on:aer=off:etr=on:add=large:afp=40000:afq=2.7725255392834085:afr=on:ins=8:bce=on_0");
    feqAtomsG180.push("lrs+1011_2605:524288_anc=none:drc=encompass:sil=128000:tgt=full:plsq=on:plsqr=195459,1048576:sp=occurrence:sos=on:abs=on:bce=on:lcm=predicate:plsql=on:st=5.5:i=6176:add=large:kws=frequency:awrs=decay:awrsf=149:uhcvi=on:ss=axioms:rawr=on:ins=2:flr=on:afp=50:afq=2.4020044236363103_0");
    feqAtomsG180.push("dis-1002_6_acc=on:anc=none:bce=on:cond=fast:drc=off:fsd=off:fde=none:gsp=on:irw=on:sac=on:sp=scramble:tgt=ground:urr=ec_only:i=77470_0");
    feqAtomsG180.push("ott+11_25:3_anc=all_dependent:bsr=unit_only:sil=64000:sp=occurrence:urr=on:rnwc=on:fd=preordered:nwc=10.0:newcnf=on:cond=fast:i=6961:sd=3:kws=inv_frequency:bd=preordered:sup=off:ss=axioms:rawr=on:avsq=on:avsqc=3:s2pl=no:s2at=2.0:fsr=off_0");
    feqAtomsG180.push("dis+1011_2:3_av=off:cond=on:ep=RS:flr=on:fsd=off:lcm=reverse:nm=0:nwc=2.5:sp=frequency:i=7334_0");
    feqAtomsG180.push("dis+11_12:7_sil=32000:sp=weighted_frequency:sos=on:urr=ec_only:lsd=1:sac=on:i=7605:bd=off:nm=2:rawr=on:nicw=on:bs=unit_only:flr=on:ss=axioms:st=2.5_0");
    feqAtomsG180.push("dis-1011_1:1_sil=16000:i=7967:fsr=off:ep=R:nm=4:fde=none_0");
    feqAtomsG180.push("dis+1002_25:43_bsr=unit_only:slsqr=1,2:sil=32000:tgt=full:plsq=on:plsqr=93,203:sp=const_min:sos=on:plsql=on:nwc=5.0:alpa=random:newcnf=on:slsq=on:nicw=on:i=31995:add=off:bs=on:slsql=off:fsr=off:uhcvi=on:acc=on_0");
    feqAtomsG180.push("lrs+1011_1:1_sil=64000:acc=on:rp=on:sac=on:newcnf=on:cond=fast:i=8225:bs=on_0");
    feqAtomsG180.push("lrs-1010_1590:949_si=on:sp=const_frequency:atotf=0.1:i=8829:nm=3:rtra=on:ss=axioms:sil=16000:kws=inv_arity_squared:sd=1:rawr=on:lcm=predicate:lma=on:spb=goal_then_units:uhcvi=on:sfv=off:awrs=decay:awrsf=40:sac=on:abs=on:bd=preordered_0");
    feqAtomsG180.push("lrs+1011_8:1_sil=128000:tgt=ground:fde=unused:sp=frequency:nwc=5.0:lwlo=on:i=32492:awrs=converge:awrsf=1385:av=off_0");
    feqAtomsG180.push("lrs-1011_2643:524288_drc=off:sil=16000:tgt=ground:plsqc=1:plsq=on:plsqr=12860815,1048576:sp=unary_first:spb=goal_then_units:urr=on:lsd=10:rnwc=on:plsql=on:nwc=5.34008:newcnf=on:cond=fast:st=4.5:i=12023:add=large:bs=unit_only:sd=5:aac=none:bd=off:nm=20:amm=sco:uhcvi=on:ss=included:alpa=false:sac=on_0");
    feqAtomsG180.push("dis-1004_46:473_drc=encompass:sil=64000:fde=unused:plsqc=1:sims=off:plsq=on:plsqr=7134431,131072:erd=off:urr=on:br=off:rp=on:avsqc=1:newcnf=on:avsq=on:i=24297:kws=frequency:nm=2:afr=on:gsp=on:plsql=on:ins=1:alpa=true:afp=1000:afq=1.906_0");
    feqAtomsG180.push("lrs+1002_1:7_drc=encompass:sil=64000:sos=on:urr=full:i=13414:sd=2:ss=axioms:sgt=100_0");
    feqAtomsG180.push("lrs-1011_1:4_drc=off:sil=128000:plsq=on:plsqr=11166605,262144:lsd=20:s2agt=100:s2a=on:i=13704:awrs=converge:awrsf=200:bd=off:sp=reverse_frequency:erd=off:gsp=on_0");
    feqAtomsG180.push("lrs+1010_1:1_sil=16000:sp=occurrence:sos=all:st=5.0:i=13774:ss=axioms:sgt=16:sd=12_0");
    feqAtomsG180.push("lrs+1002_1:1_slsqr=2,1:sil=16000:urr=full:bce=on:nwc=2.0:slsq=on:st=5.0:i=14123:sd=2:ss=axioms_0");
    feqAtomsG180.push("dis+1002_1:5_acc=on:afp=1010:fsr=off:gsp=on:nm=10:sac=on:sos=on:sp=unary_first:urr=ec_only:si=on:rawr=on:rtra=on:i=32323_0");
    feqAtomsG180.push("dis+1002_1:1_sil=16000:tgt=ground:sac=on:i=16333:sd=2:aac=none:ss=axioms:nwc=10.0_0");
    feqAtomsG180.push("dis+1010_1:3_si=on:acc=on:nwc=2.0:s2a=on:i=17452:kws=arity_squared:nm=3:rtra=on:sil=64000:bsr=unit_only:sp=frequency:alpa=false_0");
    feqAtomsG180.push("lrs+1011_2:5_bs=unit_only:fsd=off:fde=none:nm=4:nwc=5.0:sac=on:sil=128000:i=19116_0");
    feqAtomsG180.push("lrs+1011_43865:524288_sil=256000:gs=on:nwc=10.0:i=44570:av=off:rawr=on:drc=off:awrs=decay:awrsf=450_0");
    feqAtomsG180.push("dis+1011_7:15_slsqr=36,31:drc=off:sil=64000:tgt=ground:plsq=on:sp=const_frequency:spb=goal_then_units:acc=on:fd=preordered:nwc=14.322396450954507:slsqc=1:slsq=on:st=4.0:i=53338:s2at=5.0:kws=precedence:ss=axioms:rawr=on:fsr=off_0");
    feqAtomsG180.push("lrs-1011_1:16_anc=none:drc=off:sil=128000:fde=unused:rnwc=on:nwc=1.75:updr=off:s2a=on:i=37218:s2at=4.0:kws=precedence:afp=2000:bd=preordered:ins=1:afq=2.309736410117262:rawr=on:bsd=on:bsdmm=1_0");
    feqAtomsG180.push("lrs+1011_55751:262144_sil=128000:sos=on:urr=on:s2a=on:i=43983:fdi=5:gsp=on_0");

    // total_instr 1315990
    // len(covered) 2170

    Schedule feqAtomsL180propZ;

    feqAtomsL180propZ.push("lrs-1011_16:31_bsr=on:drc=encompass:tgt=full:sp=unary_first:acc=on:updr=off:nicw=on:i=134284:sil=256000:si=on:rtra=on:to=lpo:spb=goal_then_units:nwc=5.23:urr=on:lwlo=on:fdi=20:fsd=on:awrs=decay_0");
    feqAtomsL180propZ.push("ott+1011_1:3_drc=encompass:sil=256000:bsd=on:sp=occurrence:sos=on:newcnf=on:i=214065:afp=1:aac=none:amm=off:afq=3.64962_0");
    feqAtomsL180propZ.push("lrs+1010_2201:262144_anc=all:drc=encompass:sil=256000:sims=off:sp=frequency:spb=goal_then_units:rp=on:lwlo=on:st=3.0:i=231451:bs=unit_only:nm=6:ins=2:fsd=on:ss=axioms:sgt=16:afr=on:tgt=ground:awrs=decay:awrsf=200:acc=on:ccuc=first_0");

    feqAtomsL180propZ.push("dis+1011_1:1_to=lpo:sil=4000:sp=const_max:sos=all:spb=goal:st=1.5:i=103:av=off:ss=axioms:sfv=off:bd=off:sd=2:fd=off_0");
    feqAtomsL180propZ.push("dis-1002_1:2_sil=4000:i=110:nm=2:ins=3:bd=off:fsr=off:rp=on:to=lpo:nwc=5.0:fd=off:sfv=off:fs=off_0");
    feqAtomsL180propZ.push("lrs+1011_1:1_sil=32000:rnwc=on:nwc=10.0:lwlo=on:i=107:bd=off:av=off_0");
    feqAtomsL180propZ.push("lrs-1011_4:7_sil=2000:tgt=full:bsd=on:spb=goal:nwc=5.0:updr=off:newcnf=on:i=121:kws=arity_squared:rawr=on:bsdmm=2_0");
    feqAtomsL180propZ.push("lrs-21_1:1_sil=4000:sos=on:lcm=predicate:i=107:sd=2:ss=axioms_0");
    feqAtomsL180propZ.push("lrs+1011_1166409:524288_bsr=unit_only:to=lpo:drc=off:sil=2000:fde=unused:avsql=on:etr=on:sp=occurrence:spb=goal_then_units:lsd=50:rp=on:nwc=6.05391:avsqc=5:sac=on:newcnf=on:avsq=on:i=132:bs=unit_only:afp=300:aac=none:avsqr=13677,1048576:nm=0:ins=3:fsr=off:fsd=on:afq=4.16901:uhcvi=on:afr=on:rawr=on:fsdmm=3:gsp=on_0");
    feqAtomsL180propZ.push("dis-1010_1:12_sil=2000:sims=off:bce=on:nwc=2.0:newcnf=on:s2a=on:i=150:s2at=2.0:bd=off:fsr=off:irw=on:alpa=false:rawr=on:sp=occurrence_0");
    feqAtomsL180propZ.push("dis+10_52093:131072_drc=off:sil=2000:tgt=ground:irw=on:foolp=on:lma=on:urr=ec_only:nwc=5.20774:st=1.5:i=124:sd=2:kws=inv_frequency:nm=7:ins=3:av=off:uhcvi=on:ss=axioms:rawr=on_0");
    feqAtomsL180propZ.push("lrs+11_1:1024_sil=2000:spb=units:rp=on:updr=off:st=6.0:i=109:sd=3:ss=axioms:sac=on:ep=R_0");
    feqAtomsL180propZ.push("dis+1011_3:7_to=lpo:sos=on:spb=goal_then_units:abs=on:lsd=20:st=1.5:i=113:sd=2:aac=none:awrs=decay:bd=off:ss=axioms:sgt=32:flr=on:sil=256000:nm=26_0");
    feqAtomsL180propZ.push("dis+1002_1:1_sil=2000:tgt=full:spb=goal:avsq=on:i=173:avsqr=19,107:er=known:rawr=on:nwc=3.7:cond=fast:abs=on_0");
    feqAtomsL180propZ.push("lrs+1011_1:128_sil=2000:sos=on:st=3.0:i=114:sd=5:bd=off:ss=axioms:av=off_0");
    feqAtomsL180propZ.push("lrs+1011_1:1_sil=16000:fde=unused:plsqc=1:plsq=on:plsqr=32,1:sos=on:nwc=10.0:i=143:kws=frequency:nm=2:lsd=1:bd=off_0");
    feqAtomsL180propZ.push("lrs+1011_649:65536_drc=encompass:sil=2000:tgt=ground:plsqc=1:plsq=on:plsqr=8,111:sp=reverse_frequency:plsql=on:newcnf=on:i=1659:afp=50:fsr=off:afq=3.63765:afr=on:ss=axioms:sgt=16:bd=off:cond=on_0");
    feqAtomsL180propZ.push("dis-1011_1:3_nwc=10.0:s2agt=8:s2a=on:i=145:bs=on:av=off:sp=occurrence:sil=2000:si=on:rtra=on:random_seed=2126866997:updr=off:bd=off_0");
    feqAtomsL180propZ.push("dis+1011_543:505_drc=encompass:sil=128000:tgt=full:etr=on:sp=frequency:nwc=4.8:avsqc=4:sac=on:avsq=on:st=7.0:i=151:kws=precedence:avsqr=2669309,1048576:awrs=converge:awrsf=975:bd=off:nm=16:ss=axioms:rawr=on:bsd=on:add=large_0");
    feqAtomsL180propZ.push("lrs+21_1:5_sil=2000:sos=on:urr=on:newcnf=on:slsq=on:i=224:slsql=off:bd=off:nm=2:ss=axioms:st=1.5:sp=const_min:gsp=on:rawr=on_0");
    feqAtomsL180propZ.push("lrs+1002_1:1_sfv=off:drc=encompass:sil=2000:fde=unused:sp=frequency:nwc=10.0:flr=on:st=1.5:i=226:bd=off:nm=0:ins=4:fsr=off:fsd=on:ss=axioms:s2a=on:s2agt=32:to=lpo:aac=none:sims=off_0");
    feqAtomsL180propZ.push("lrs+1010_1:4_sil=2000:tgt=ground:sp=reverse_frequency:nwc=5.0:i=206:av=off:bd=off:kmz=on_0");
    feqAtomsL180propZ.push("dis+1011_1:4_bsr=on:to=lpo:sil=2000:tgt=ground:plsqc=1:plsq=on:plsqr=4477983,65536:sp=frequency:erd=off:spb=goal:nwc=2.0:sac=on:newcnf=on:cond=fast:st=5.0:i=251:nm=16:ss=axioms:rawr=on:lsd=100:awrs=converge_0");
    feqAtomsL180propZ.push("lrs-1011_1:1_to=lpo:drc=off:sil=2000:sp=const_min:sos=on:lsd=10:sac=on:i=271:br=off:newcnf=on_0");
    feqAtomsL180propZ.push("lrs+1011_8:13_slsqr=96,997:drc=off:sil=64000:sp=const_max:spb=goal_then_units:rnwc=on:nwc=5.0:slsq=on:cond=on:i=285:kws=precedence:rawr=on:fd=preordered:av=off:bs=unit_only_0");
    feqAtomsL180propZ.push("lrs+1011_16:1_to=lpo:sil=2000:spb=goal_then_units:urr=on:lsd=1:i=285:bd=off:ss=axioms:gsp=on:sac=on_0");
    feqAtomsL180propZ.push("dis-1002_1:1_to=lpo:drc=encompass:sil=2000:sp=const_max:nwc=10.0:s2a=on:i=286:s2at=2.0:afp=10:ins=16:afq=1.4:aac=none:rawr=on:fsr=off:alpa=true_0");
    feqAtomsL180propZ.push("lrs+1002_1:1_to=lpo:drc=encompass:sil=4000:sp=const_min:sos=on:spb=goal_then_units:acc=on:urr=on:sac=on:avsq=on:i=314:ins=2:br=off_0");
    feqAtomsL180propZ.push("dis-11_101:15_to=lpo:sil=4000:tgt=full:fde=none:sp=const_frequency:acc=on:sac=on:avsq=on:i=332:avsqr=16429,1048576:bd=off:nm=16:er=filter:spb=goal:anc=all_dependent:slsq=on:slsql=off:slsqc=4:s2at=5.0:alpa=true_0");
    feqAtomsL180propZ.push("dis-30_282927:1048576_sfv=off:sil=2000:etr=on:sp=unary_first:spb=goal_then_units:abs=on:nwc=11.1969:s2agt=100:kmz=on:cond=fast:st=3:s2a=on:i=641:s2at=1.5:add=large:sd=4:bd=off:nm=25:fsr=off:fsd=on:gsp=on:ss=axioms:er=known:rawr=on:alpa=random:lma=on_0");
    feqAtomsL180propZ.push("lrs-10_1:40_bsr=unit_only:sil=4000:tgt=ground:lcm=reverse:fd=preordered:s2a=on:i=681:s2at=3.0:rawr=on:kws=inv_frequency:fsr=off_0");
    feqAtomsL180propZ.push("lrs+1011_1:1024_sil=4000:br=off:i=757:bd=off:fd=preordered:slsq=on:slsql=off:slsqc=2:slsqr=1,4:s2at=4.0_0");
    feqAtomsL180propZ.push("dis-1010_1:4_sil=2000:tgt=ground:i=906:sd=2:nm=6:av=off:gsp=on:ss=axioms:nwc=10.0_0");
    feqAtomsL180propZ.push("lrs-32_2:11_drc=encompass:sil=4000:sp=reverse_frequency:nwc=10.0:s2a=on:i=2306:s2at=5.0:nm=16:amm=sco_0");
    feqAtomsL180propZ.push("lrs+1011_1574893:524288_to=lpo:drc=encompass:sil=4000:sp=const_frequency:spb=goal:fd=preordered:nwc=7.0:alpa=false:sac=on:newcnf=on:cond=fast:s2a=on:i=688:s2at=4.0:bd=preordered:awrs=decay:awrsf=60:sfv=off_0");
    feqAtomsL180propZ.push("lrs-32_1:4_to=lpo:drc=off:sil=2000:sp=reverse_arity:spb=goal_then_units:urr=on:nwc=2.0:i=1150:ss=included:st=2.0:bd=preordered_0");
    feqAtomsL180propZ.push("dis+11_1:7_sil=2000:tgt=ground:sp=reverse_arity:i=1934:fd=preordered:fsr=off:drc=encompass_0");
    feqAtomsL180propZ.push("lrs+2_5:1_slsqr=30,127:to=lpo:drc=off:sil=128000:tgt=full:sp=const_min:fd=preordered:nwc=5.0:slsq=on:i=6132:slsql=off:ins=2:ss=axioms:rawr=on:slsqc=1:plsq=on:plsqc=2:fdi=1:st=2.0:plsql=on_0");
    feqAtomsL180propZ.push("lrs+1011_1:128_drc=encompass:sil=32000:tgt=full:fde=none:sp=weighted_frequency:nwc=1.5:i=7322:kws=inv_arity_squared:awrs=converge_0");
    feqAtomsL180propZ.push("lrs-4_1:24_slsqr=493885,1048576:drc=encompass:sil=128000:tgt=full:sp=weighted_frequency:fd=preordered:flr=on:slsq=on:i=54457:bs=unit_only:av=off:fsr=off:rawr=on_0");
    feqAtomsL180propZ.push("lrs+1011_4:1_to=lpo:sil=16000:fde=none:plsq=on:plsqr=1,8:sp=occurrence:st=2.0:i=9562:sd=3:ss=axioms:er=known:av=off:awrs=converge:awrsf=500:fsr=off_0");
    feqAtomsL180propZ.push("lrs+21_1:6_to=lpo:drc=off:sil=64000:tgt=ground:fd=preordered:i=15240_0");
    feqAtomsL180propZ.push("lrs+1011_1:6_to=lpo:drc=encompass:sil=256000:tgt=full:sp=unary_first:nwc=10.0:i=19986:aac=none:bd=preordered:ss=axioms:sgt=16_0");
    feqAtomsL180propZ.push("lrs+21_1:64_drc=encompass:sil=32000:bsd=on:lma=on:spb=goal:nwc=10.0:i=22098:add=large:ss=axioms:sgt=16:irw=on_0");
    feqAtomsL180propZ.push("lrs+35_1:1_to=lpo:sil=128000:tgt=full:fd=preordered:lwlo=on:i=119085:bd=preordered:drc=off:av=off_0");
    feqAtomsL180propZ.push("lrs+11_1:20_drc=off:sil=128000:tgt=ground:fde=none:sp=const_min:spb=goal:nwc=1.08:i=126497:bd=off:rawr=on:fsr=off:ss=axioms:sgt=32:kws=frequency:bs=unit_only:urr=ec_only_0");
    feqAtomsL180propZ.push("dis+1010_19:119_sil=256000:tgt=ground:sp=reverse_frequency:spb=units:acc=on:rp=on:nwc=0.74658:cond=on:i=74983:add=large:bs=on:kws=inv_arity:bd=off:ins=1:amm=sco:rawr=on:anc=none_0");

    // total_instr 1050466
    // len(covered) 274

    Schedule feqAtomsL180propNZatomsG50;

    feqAtomsL180propNZatomsG50.push("lrs+2_5:39_bsr=unit_only:to=lpo:drc=off:sil=128000:plsq=on:plsqr=2,19:sp=frequency:lcm=reverse:fd=preordered:s2a=on:i=38749:s2at=-1.0:fsr=off:uhcvi=on:rawr=on:aer=off:lwlo=on:add=off:bce=on:acc=model:afr=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+1002_74:59_drc=off:tgt=full:sos=all:cond=fast:i=124987:kws=inv_frequency:afp=300:afq=2.0744697298148953:rawr=on:urr=full:sil=128000:si=on:rtra=on:random_seed=3250543_0");
    feqAtomsL180propNZatomsG50.push("lrs+11_1:16_to=lpo:drc=off:bsd=on:sp=frequency:i=172350:bs=on:av=off:fsd=on:sil=256000:fdi=50_0");

    feqAtomsL180propNZatomsG50.push("lrs+1011_1:1_sil=2000:i=103:ep=RS:nm=32:ss=axioms:sos=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_1:1_sil=32000:rnwc=on:nwc=10.0:lwlo=on:i=121:bd=off:av=off_0");
    feqAtomsL180propNZatomsG50.push("dis-1011_2:1_sil=2000:lsd=20:nwc=5.0:flr=on:mep=off:st=3.0:i=113:sd=1:ep=RS:ss=axioms_0");
    feqAtomsL180propNZatomsG50.push("lrs+1010_1:1_to=lpo:sil=2000:plsq=on:plsqr=32,1:sp=reverse_arity:sos=on:spb=goal_then_units:i=128:ss=axioms:sgt=50:bd=off:sd=3_0");
    feqAtomsL180propNZatomsG50.push("lrs+1002_1:1024_drc=encompass:sil=2000:tgt=full:rp=on:i=123:nm=16:ss=axioms:sd=1:st=2.0_0");
    feqAtomsL180propNZatomsG50.push("lrs+10_1:1_sil=8000:sp=occurrence:sos=on:urr=full:nwc=10.0:st=1.5:i=205:ss=axioms:rnwc=on:sgt=4_0");
    feqAtomsL180propNZatomsG50.push("ott+1011_1:3_drc=off:sil=4000:tgt=ground:fde=unused:plsq=on:sp=unary_first:fd=preordered:nwc=10.0:i=180:ins=1:rawr=on:bd=preordered_0");
    feqAtomsL180propNZatomsG50.push("ott+1002_2835555:1048576_to=lpo:sil=2000:sos=on:fs=off:nwc=10.3801:avsqc=3:updr=off:avsq=on:st=2:s2a=on:i=143:s2at=3:afp=10000:aac=none:avsqr=13357983,1048576:awrs=converge:awrsf=460:bd=off:nm=13:ins=2:fsr=off:amm=sco:afq=1.16719:ss=axioms:rawr=on:fd=off_0");
    feqAtomsL180propNZatomsG50.push("lrs+2_1:1_sil=16000:fde=none:sos=all:nwc=5.0:i=113:ep=RS:s2pl=on:lma=on:afp=100000_0");
    feqAtomsL180propNZatomsG50.push("dis-1011_3:14_sil=32000:rp=on:nwc=7.0:sac=on:mep=off:s2a=on:i=113:ep=R:gsp=on:rawr=on:awrs=converge:awrsf=47:s2agt=30:rnwc=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_1:1024_sil=2000:sos=on:lsd=10:i=114:sd=3:kws=frequency:bd=off:nm=6:av=off:gsp=on:ss=axioms:sgt=64:fde=unused_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_1:4_sil=2000:tgt=ground:lsd=100:nwc=2.0:st=7.0:i=253:bd=off:nm=16:av=off:ss=axioms:rawr=on_0");
    feqAtomsL180propNZatomsG50.push("ott-32_5:1_sil=4000:sp=occurrence:urr=full:rp=on:nwc=5.0:newcnf=on:st=5.0:s2pl=on:i=150:sd=2:ins=2:ss=included:rawr=on:anc=none:sos=on:s2agt=8:spb=intro:ep=RS:avsq=on:avsqr=27,155:lma=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+1010_1:1_tgt=ground:fde=unused:sp=const_frequency:nwc=5.0:sac=on:avsq=on:i=196:avsqr=1,8:fsd=on:sil=64000:gs=on:rnwc=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+1002_1:1_sil=4000:i=107:sd=2:ep=RS:av=off:ss=axioms:sos=on:erd=off_0");
    feqAtomsL180propNZatomsG50.push("lrs+10_1:1024_sil=2000:st=2.0:i=107:sd=2:ss=included:ep=R_0");
    feqAtomsL180propNZatomsG50.push("ott+10_107421:1048576_to=lpo:drc=off:sil=4000:fde=none:sos=on:lma=on:spb=intro:gs=on:nwc=24.2524:gsem=off:i=147:sd=3:afp=40000:awrs=decay:awrsf=1166:nm=6:afq=1.99252:uhcvi=on:ss=axioms:rawr=on:sp=const_max:add=off_0");
    feqAtomsL180propNZatomsG50.push("dis+1002_1:2_to=lpo:sil=2000:sos=on:abs=on:newcnf=on:i=116:sd=1:bd=off:ss=included:rawr=on:sp=const_frequency:fsr=off:fs=off_0");
    feqAtomsL180propNZatomsG50.push("ott-1011_16:1_sil=2000:sp=const_max:urr=on:lsd=20:st=3.0:i=304:ss=axioms:gsp=on:rp=on:sos=on:fd=off:aac=none_0");
    feqAtomsL180propNZatomsG50.push("ott+1011_9:29_slsqr=3,2:sil=2000:tgt=ground:lsd=10:lcm=predicate:avsqc=4:slsq=on:avsq=on:i=135:s2at=4.0:add=large:sd=1:avsqr=1,16:aer=off:ss=axioms:sgt=100:rawr=on:s2a=on:sac=on:afp=1:nwc=10.0:nm=64:bd=preordered:abs=on:rnwc=on:er=filter:nicw=on:spb=non_intro:lma=on_0");
    feqAtomsL180propNZatomsG50.push("dis+1010_1:1_sil=2000:urr=on:lcm=predicate:i=261:ile=on:gs=on:br=off_0");
    feqAtomsL180propNZatomsG50.push("lrs+21_1:1_to=lpo:sil=2000:sp=const_min:st=3.0:i=109:sd=1:erml=4:ss=axioms:er=filter:alpa=true:amm=sco:bd=off_0");
    feqAtomsL180propNZatomsG50.push("dis+1011_5:1_sil=2000:fde=unused:nwc=10.0:i=118:ep=R:fs=off:fsr=off:awrs=converge_0");
    feqAtomsL180propNZatomsG50.push("lrs-21_1:1_sil=4000:sos=on:lcm=predicate:i=109:sd=2:ss=axioms_0");
    feqAtomsL180propNZatomsG50.push("lrs+32_1:128_drc=off:sil=2000:tgt=ground:flr=on:i=119:fsr=off_0");
    feqAtomsL180propNZatomsG50.push("dis+1002_1:1_sil=2000:sos=on:sac=on:st=5.0:i=213:ss=axioms_0");
    feqAtomsL180propNZatomsG50.push("dis+10_78677:524288_anc=all_dependent:sil=4000:irw=on:fde=unused:plsq=on:plsqr=4929279,131072:etr=on:sp=const_max:sos=all:spb=goal_then_units:lcm=predicate:fd=off:nwc=6.051592140664891:i=126:sd=3:kws=inv_arity_squared:afp=40000:bd=off:nm=6:afq=1.82720764930041:ss=axioms:rawr=on:bsr=on:newcnf=on:bs=unit_only:abs=on:ins=4:gsp=on:rnwc=on:awrs=decay:awrsf=179:s2a=on:s2agt=10:s2at=4.0:st=5.0:foolp=on:afr=on_0");
    feqAtomsL180propNZatomsG50.push("dis+1011_1:20_sil=2000:tgt=full:fde=unused:sos=on:i=301:kws=inv_arity_squared:aac=none_0");
    feqAtomsL180propNZatomsG50.push("dis+1010_3:2_sil=4000:plsq=on:s2agt=100:sac=on:s2a=on:i=115:s2at=2.0:ep=RS:tgt=full_0");
    feqAtomsL180propNZatomsG50.push("dis+1011_5:2_to=lpo:sil=8000:tgt=ground:plsq=on:plsqr=65749,1048576:spb=goal:nwc=10.0:newcnf=on:i=335:rawr=on:av=off:nm=5:awrs=converge:awrsf=340:bsd=on:s2a=on:fdi=1_0");
    feqAtomsL180propNZatomsG50.push("lrs+21_1:5_sil=2000:sos=on:urr=on:newcnf=on:slsq=on:i=484:slsql=off:bd=off:nm=2:ss=axioms:st=1.5:sp=const_min:gsp=on:rawr=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+1010_1:512_sil=8000:tgt=ground:spb=units:gs=on:lwlo=on:nicw=on:gsem=on:st=1.5:i=120:nm=21:ss=included:nwc=5.3:afp=4000:afq=1.38:ins=1:bs=unit_only:awrs=converge:awrsf=10:bce=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+21_2461:262144_anc=none:drc=off:sil=2000:sp=occurrence:nwc=6.0:updr=off:st=3.0:i=141:sd=2:afp=4000:erml=3:nm=14:afq=2.0:uhcvi=on:ss=included:er=filter:abs=on:nicw=on:ile=on:sims=off:s2a=on:s2agt=50:s2at=-1.0:plsq=on:plsql=on:plsqc=2:plsqr=1,32:newcnf=on:bd=off:to=lpo_0");
    feqAtomsL180propNZatomsG50.push("dis+1010_3:1_sil=4000:bce=on:s2agt=15:st=5.0:s2a=on:i=168:sd=1:ep=RS:ss=axioms:plsq=on:plsqc=1:plsqr=24176865,524288:fsr=off_0");
    feqAtomsL180propNZatomsG50.push("dis-1010_1:8_sil=256000:i=123:nm=16:av=off:erd=off:sfv=off:fd=off:bd=off_0");
    feqAtomsL180propNZatomsG50.push("dis+1003_1:1024_sil=4000:urr=on:newcnf=on:i=172:av=off:fsr=off:bce=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_4:1_bsr=on:sil=32000:sos=all:urr=on:br=off:s2a=on:i=336:s2at=2.0:bd=off:gsp=on:ss=axioms:sgt=8:sd=1:fsr=off_0");
    feqAtomsL180propNZatomsG50.push("lrs-1011_8:1_sil=2000:spb=goal:urr=on:sac=on:i=129:afp=10000:fsr=off:ss=axioms:avsq=on:avsqr=17819,524288:bd=off:bsd=on:fd=off:sims=off:rawr=on:alpa=true:bsr=on:aer=off_0");
    feqAtomsL180propNZatomsG50.push("dis+10_3:31_sil=2000:sp=frequency:abs=on:acc=on:lcm=reverse:nwc=3.0:alpa=random:st=3.0:i=219:sd=1:nm=4:ins=1:aer=off:ss=axioms_0");
    feqAtomsL180propNZatomsG50.push("lrs+10_1:52_anc=all:bsr=unit_only:to=lpo:sil=2000:sp=frequency:fd=preordered:flr=on:sac=on:i=571:bd=off:alpa=true:plsq=on:plsqr=1,32_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_2:3_sil=16000:sos=on:rp=on:newcnf=on:lwlo=on:st=1.5:i=205:sd=2:bd=off:nm=2:fsr=off:gsp=on:ss=axioms:bce=on:anc=all:sac=on_0");
    feqAtomsL180propNZatomsG50.push("dis+10_8:1_to=lpo:sil=64000:tgt=ground:fde=unused:sp=const_max:sos=all:spb=goal:s2a=on:i=136:sd=4:nm=32:ss=axioms:fs=off:fsr=off:sfv=off:alpa=true_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_55751:262144_sil=128000:sos=on:urr=on:s2a=on:i=173:fdi=5:gsp=on_0");
    feqAtomsL180propNZatomsG50.push("dis+10_1:4_to=lpo:sil=2000:sos=on:spb=goal:rp=on:sac=on:newcnf=on:i=247:ss=axioms:aac=none_0");
    feqAtomsL180propNZatomsG50.push("lrs-21_1:1_to=lpo:sil=2000:sp=frequency:sos=on:lma=on:i=137:sd=2:ss=axioms:ep=R_0");
    feqAtomsL180propNZatomsG50.push("dis+1010_12107:524288_anc=none:drc=encompass:sil=2000:bsd=on:rp=on:nwc=10.0:alpa=random:i=216:kws=precedence:awrs=decay:awrsf=2:nm=16:ins=3:rawr=on:s2a=on:s2at=4.5:acc=on:flr=on_0");
    feqAtomsL180propNZatomsG50.push("dis-1002_1:12_to=lpo:sil=2000:sp=const_max:nwc=2.0:sac=on:i=278:nm=16:nicw=on:fsr=off_0");
    feqAtomsL180propNZatomsG50.push("dis+1011_2:3_sil=2000:tgt=ground:fde=none:sos=on:lsd=1:alpa=random:i=234:kws=inv_arity_squared:gsp=on:bsd=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+1002_1:8_sil=2000:tgt=ground:lcm=reverse:rp=on:i=336:sd=1:nm=6:ss=axioms:flr=on:bd=off_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_1:8_bsr=unit_only:drc=encompass:sil=128000:fde=none:avsql=on:sp=frequency:sos=all:spb=goal:rnwc=on:nwc=10.0:avsqc=3:avsq=on:s2a=on:i=148:kws=precedence:awrs=converge:awrsf=500:amm=off:rawr=on:bce=on:newcnf=on:ss=included:sd=1:sgt=20:bsd=on:fsr=off:nicw=on_0");
    feqAtomsL180propNZatomsG50.push("dis+1002_1:1_sil=2000:tgt=full:spb=goal:avsq=on:i=206:avsqr=19,107:er=known:rawr=on:nwc=3.7:cond=fast:abs=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_1:4_bsr=unit_only:to=lpo:sil=2000:plsqc=4:plsq=on:sp=occurrence:plsql=on:alpa=false:i=156:afp=10:afq=2.0:ss=axioms:rawr=on:fd=off_0");
    feqAtomsL180propNZatomsG50.push("lrs+1010_1:4_sil=2000:tgt=ground:sp=reverse_frequency:nwc=5.0:i=374:av=off:bd=off:kmz=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_4:1_to=lpo:drc=off:sil=8000:sp=frequency:abs=on:urr=on:lsd=10:nwc=5.0:s2agt=4:newcnf=on:st=5.0:s2a=on:i=673:ss=axioms:aac=none:br=off:bd=preordered_0");
    feqAtomsL180propNZatomsG50.push("lrs+11_1:1_sos=on:urr=on:s2a=on:i=318:sd=1:aac=none:ss=axioms:gsp=on:sil=128000:nm=3:bce=on:fd=preordered:alpa=true:etr=on:bd=off:lcm=predicate_0");
    feqAtomsL180propNZatomsG50.push("lrs-1011_1:16_drc=off:sil=128000:fde=none:fs=off:abs=on:acc=on:lsd=50:flr=on:newcnf=on:s2a=on:i=248:sd=2:fsr=off:ss=included:awrs=decay:awrsf=200:nwc=2.0_0");
    feqAtomsL180propNZatomsG50.push("lrs-1011_1:1_sil=2000:sos=on:urr=on:i=174:sd=1:bd=off:ins=3:av=off:ss=axioms:sgt=16:gsp=on:lsd=10_0");
    feqAtomsL180propNZatomsG50.push("lrs+1002_263:262144_sfv=off:to=lpo:drc=encompass:sil=2000:tgt=full:fde=none:bsd=on:sp=const_frequency:spb=units:fd=preordered:nwc=12.504039574721643:lwlo=on:i=180:awrs=converge:awrsf=1360:bsdmm=3:bd=off:nm=11:fsd=on:amm=off:uhcvi=on:afr=on:rawr=on:fsdmm=1:updr=off:sac=on:fdi=16_0");
    feqAtomsL180propNZatomsG50.push("dis-11_4:1_to=lpo:sil=2000:fde=unused:sims=off:sp=occurrence:lma=on:spb=goal_then_units:abs=on:fd=off:flr=on:avsq=on:i=260:avsqr=1137305,524288:bd=off:uhcvi=on:awrs=decay:sos=on:bsd=on:afp=50:afq=1.3:nwc=10.053150171695567_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_1:2_drc=off:sil=16000:tgt=ground:sp=reverse_arity:spb=goal:nwc=10.0:lwlo=on:st=2.0:i=181:kws=precedence:ss=axioms_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_1:1_sil=64000:i=182:sd=2:ep=R:ss=axioms_0");
    feqAtomsL180propNZatomsG50.push("lrs+1010_1:28_plsqc=4:si=on:plsq=on:plsqr=22387283,262144:i=347:sd=2:rtra=on:ss=included:sgt=8:sil=2000:slsq=on:slsqc=1:nm=32:acc=model:aer=off:alpa=false:spb=intro:nicw=on:bd=off:sp=reverse_arity:kws=arity_0");
    feqAtomsL180propNZatomsG50.push("dis+1002_1:2_to=lpo:sil=2000:sp=unary_first:newcnf=on:i=183:aac=none:nm=2:fsr=off_0");
    feqAtomsL180propNZatomsG50.push("lrs+35_1:7_sil=2000:tgt=full:fde=unused:sp=occurrence:sos=on:st=3.5:s2pl=no:i=183:bd=off:nm=16:fsr=off:uhcvi=on:ss=axioms:rawr=on_0");
    feqAtomsL180propNZatomsG50.push("dis-1011_1785:1048576_bsr=unit_only:sil=4000:tgt=ground:plsqc=1:plsq=on:plsqr=125493,524288:sp=frequency:spb=goal:plsql=on:nwc=2.32086:updr=off:newcnf=on:cond=fast:st=2:s2a=on:i=193:s2at=4:bd=off:nm=3:ins=3:aer=off:uhcvi=on:afr=on:ss=axioms:sgt=20:rawr=on:fsr=off_0");
    feqAtomsL180propNZatomsG50.push("dis-1011_443601:1048576_to=lpo:drc=off:sil=2000:fde=unused:bsd=on:etr=on:sp=reverse_frequency:erd=off:spb=goal_then_units:bce=on:nwc=21.6966:newcnf=on:nicw=on:cond=on:i=195:bsdmm=2:nm=14:ins=2:uhcvi=on:fdi=2:rnwc=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+11_857975:262144_bsr=unit_only:drc=encompass:sil=4000:tgt=ground:plsqc=1:sims=off:plsq=on:plsqr=18723,262144:sp=frequency:sos=on:foolp=on:spb=units:abs=on:rnwc=on:plsql=on:gs=on:nwc=4.36781:updr=off:sac=on:cond=on:i=197:bs=unit_only:gsaa=from_current:sd=1:kws=arity_squared:afp=300:aac=none:erml=2:awrs=decay:awrsf=763:bd=off:nm=3:fsr=off:afq=4.10223:ss=included:er=filter:sgt=50_0");
    feqAtomsL180propNZatomsG50.push("lrs+10_4927:1048576_anc=none:sfv=off:slsqr=66837,32768:drc=encompass:sil=2000:tgt=full:fde=none:etr=on:sp=const_max:sos=on:erd=off:spb=goal_then_units:nwc=15.0003:s2agt=30:flr=on:avsqc=3:slsq=on:avsq=on:i=197:s2at=5.5:add=large:bs=unit_only:sd=1:aac=none:erml=3:avsqr=638249,524288:awrs=decay:awrsf=2:bd=off:nm=3:amm=sco:afr=on:gsp=on:ss=included:er=known:rawr=on:s2a=on_0");
    feqAtomsL180propNZatomsG50.push("lrs-1011_1:64_sil=2000:tgt=full:acc=on:urr=ec_only:sac=on:i=201:nm=2:ss=axioms:sgt=4:er=filter_0");
    feqAtomsL180propNZatomsG50.push("lrs-1011_1:64_slsqr=1674187,131072:sil=4000:plsq=on:lsd=50:plsql=on:slsq=on:i=202:slsql=off:bd=off:nm=3:amm=off:gsp=on:ss=axioms:fsr=off_0");
    feqAtomsL180propNZatomsG50.push("dis+1010_19:119_sil=256000:tgt=ground:sp=reverse_frequency:spb=units:acc=on:rp=on:nwc=0.74658:cond=on:i=204:add=large:bs=on:kws=inv_arity:bd=off:ins=1:amm=sco:rawr=on:anc=none_0");
    feqAtomsL180propNZatomsG50.push("lrs+21_16:1_bsr=unit_only:to=lpo:sp=const_frequency:sos=on:urr=on:newcnf=on:i=311:fsr=off:ss=axioms:alpa=true:ep=RST:sil=8000:sac=on:spb=non_intro_0");
    feqAtomsL180propNZatomsG50.push("lrs+1002_1:4_bsr=unit_only:to=lpo:sil=2000:sos=all:rp=on:avsq=on:i=207:fsr=off:rawr=on:alpa=true:flr=on:lcm=reverse:avsqc=1:nicw=on:newcnf=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+21_1:16_sil=2000:sp=occurrence:urr=on:flr=on:i=323:sd=1:nm=0:ins=3:ss=included:rawr=on:br=off_0");
    feqAtomsL180propNZatomsG50.push("dis-1011_5:4_sil=4000:fde=unused:nwc=10.0:s2a=on:i=215:nm=16:ss=included:sd=2:fsr=off_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_1:64_sil=2000:fde=none:sos=on:urr=ec_only:nwc=10.0:i=218:nm=19:gsp=on:ss=axioms:bd=off_0");
    feqAtomsL180propNZatomsG50.push("dis+1011_16:1_slsqr=5605329,524288:to=lpo:sil=4000:rp=on:slsqc=1:slsq=on:i=684:bd=off:fsr=off:lsd=50_0");
    feqAtomsL180propNZatomsG50.push("lrs-1011_1:1_sil=16000:plsq=on:plsqr=10230343,1048576:sos=on:lsd=20:sac=on:s2a=on:i=248:bd=off:ss=axioms:rawr=on:bce=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_1:14_sil=4000:sos=on:lsd=20:i=412:nm=5:rawr=on:avsq=on:avsqc=1:avsqr=5,3:urr=on:lcm=predicate:alpa=random_0");
    feqAtomsL180propNZatomsG50.push("lrs-21_1:28_sil=4000:tgt=full:sp=frequency:lma=on:urr=ec_only:nwc=3.0:sac=on:i=263:sd=1:bd=off:ss=axioms:sgt=4:rawr=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+35_10:1_bsr=unit_only:to=lpo:sil=2000:bsd=on:sp=unary_first:abs=on:urr=on:s2agt=32:newcnf=on:s2a=on:i=644:gsp=on:rawr=on:sac=on:afp=1000:avsq=on:avsqr=63937,1048576:nwc=10.0_0");
    feqAtomsL180propNZatomsG50.push("ott+2_27871:262144_drc=encompass:sil=2000:plsqc=1:plsq=on:ile=on:plsqr=9426019,262144:sp=const_frequency:foolp=on:bce=on:rnwc=on:gs=on:nwc=12.5427:i=297:gsaa=from_current:erml=3:bd=off:nm=10:uhcvi=on:gsp=on:er=known:rawr=on:fd=preordered:alpa=true_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_1:16_sil=2000:urr=on:gs=on:s2agt=8:slsqc=2:slsq=on:i=304:bd=off:rawr=on:s2a=on:fsr=off:bce=on:flr=on_0");
    feqAtomsL180propNZatomsG50.push("dis+1010_1:4_aac=none:abs=on:atotf=0.5:avsq=on:avsqc=2:avsqr=215,247:awrs=converge:awrsf=128:bsd=on:erd=off:fde=none:gve=cautious:newcnf=on:nwc=5.0:rnwc=on:sac=on:sas=z3:sp=const_min:tgt=ground:thsq=on:thsqc=64:thsqr=1,4:si=on:rawr=on:rtra=on:i=1158_0");
    feqAtomsL180propNZatomsG50.push("ott+21_2515:262144_drc=off:sil=4000:ile=on:sp=reverse_arity:lma=on:spb=goal_then_units:bce=on:nwc=1.56136:i=3621:add=large:kws=precedence:nm=34:afr=on:gsp=on:rawr=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+32_1:4_sil=2000:sos=on:rp=on:i=328:bd=off:nm=16:awrs=decay:awrsf=500_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_1:2_to=lpo:sil=8000:plsqc=1:plsq=on:plsqr=326,59:sp=weighted_frequency:plsql=on:nwc=10.0:newcnf=on:i=332:awrs=converge:awrsf=200:bd=off:ins=1:rawr=on:alpa=false:avsq=on:avsqr=1,16_0");
    feqAtomsL180propNZatomsG50.push("dis+1010_1:3_sil=2000:sos=on:erd=off:nwc=3.0:i=358:nm=0_0");
    feqAtomsL180propNZatomsG50.push("ott+1011_170061:1048576_to=lpo:drc=encompass:sil=4000:tgt=full:fde=unused:sims=off:sp=unary_frequency:lma=on:gs=on:nwc=3.05078:sac=on:nicw=on:gsem=off:s2a=on:i=372:bs=on:nm=16:ins=7:fsr=off:amm=sco:uhcvi=on:fdi=4:rawr=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+11_1:20_sil=2000:fde=none:sp=unary_first:sos=on:lma=on:spb=goal:lsd=20:i=1955:bd=off:nm=0:aer=off:kws=inv_arity_squared:rawr=on_0");
    feqAtomsL180propNZatomsG50.push("dis-1002_1:1_to=lpo:drc=encompass:sil=2000:sp=const_max:nwc=10.0:s2a=on:i=432:s2at=2.0:afp=10:ins=16:afq=1.4:aac=none:rawr=on:fsr=off:alpa=true_0");
    feqAtomsL180propNZatomsG50.push("dis+11_1:32_to=lpo:drc=encompass:sil=8000:i=1778:av=off:bs=on:bsd=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+3_1:1024_to=lpo:erd=off:spb=goal:urr=on:cond=fast:i=1334:awrs=converge:awrsf=330:av=off:ss=axioms:sgt=16:sup=off:gsp=on:sd=1:sil=32000:nwc=5.0_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_3:25_anc=all_dependent:drc=off:sil=2000:tgt=full:bsd=on:spb=goal:bce=on:nwc=4.3:avsqc=1:avsq=on:st=3.0:i=586:afp=10:aer=off:afq=4.97351:afr=on:ss=axioms:rawr=on:acc=on:rp=on:bsr=on:sp=unary_frequency_0");
    feqAtomsL180propNZatomsG50.push("lrs+10_23:15_sil=2000:plsqc=1:plsq=on:plsqr=4106395,32768:plsql=on:nwc=3.0:flr=on:newcnf=on:i=609:kws=precedence:fsr=off:ss=included_0");
    feqAtomsL180propNZatomsG50.push("dis+1011_16447:524288_slsqr=7559,1048576:drc=encompass:sil=2000:tgt=ground:sp=const_max:spb=goal:urr=ec_only:rp=on:nwc=3.04172:s2agt=100:slsqc=1:flr=on:updr=off:slsq=on:st=6:i=1627:s2at=4.5:bd=off:nm=12:ins=2:uhcvi=on:ss=axioms:sgt=20:rawr=on:rnwc=on_0");
    feqAtomsL180propNZatomsG50.push("lrs-1011_16:1_bsr=unit_only:to=lpo:sil=64000:plsqc=1:plsq=on:plsqr=48239893,524288:sp=frequency:sos=on:urr=full:rnwc=on:fd=preordered:nwc=10.0:newcnf=on:slsq=on:cond=on:i=612:slsql=off:bd=off:rawr=on:alpa=false:nm=2:ins=1_0");
    feqAtomsL180propNZatomsG50.push("dis-1010_1:1_drc=encompass:sil=2000:plsq=on:plsqr=128389,524288:sp=const_min:i=631_0");
    feqAtomsL180propNZatomsG50.push("lrs+1002_1:1024_slsqr=24,7:sil=4000:bsd=on:newcnf=on:slsq=on:st=2.0:i=691:s2at=2.5:awrs=converge:awrsf=340:ss=axioms:rawr=on:alpa=random:nicw=on:bs=unit_only_0");
    feqAtomsL180propNZatomsG50.push("dis+11_1:50_to=lpo:sil=64000:fd=preordered:i=1927:av=off:sup=off:sp=const_frequency:bd=preordered_0");
    feqAtomsL180propNZatomsG50.push("lrs+1002_1:7_to=lpo:drc=encompass:sil=2000:tgt=full:sp=reverse_arity:spb=non_intro:fd=preordered:nwc=10.0:st=3.0:i=715:ins=2:ss=axioms_0");
    feqAtomsL180propNZatomsG50.push("dis+2_1:1024_sil=8000:i=5884:kws=precedence:ss=included:sgt=32:rawr=on:sp=unary_frequency:drc=off_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_3:1_slsqr=1,2:sil=2000:tgt=full:plsq=on:plsqr=173,396:spb=goal:bce=on:newcnf=on:slsq=on:st=3.5:i=803:add=off:bs=on:fsr=off:ss=axioms:rawr=on:afp=1:afq=2.9664927043397338_0");
    feqAtomsL180propNZatomsG50.push("lrs+1010_1:56_slsqr=3,4:tgt=ground:slsqc=1:slsq=on:i=855:s2at=2.0:bd=off:amm=sco:sac=on:kws=inv_frequency:nwc=2.4:sil=4000:sfv=off:ss=axioms:sgt=32_0");
    feqAtomsL180propNZatomsG50.push("lrs+21_6:7_to=lpo:drc=off:sil=32000:tgt=full:fde=unused:bsd=on:sp=const_frequency:fd=preordered:i=930:rawr=on:bd=preordered_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_1:32_sil=2000:tgt=ground:acc=model:lsd=10:nwc=1.1:flr=on:s2pl=no:i=1070:bd=off:gsp=on:rawr=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+21_1:1_sil=64000:sos=all:urr=on:br=off:s2a=on:i=1184:sd=1:kws=inv_frequency:ss=included_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_24:11_drc=encompass:sil=2000:tgt=ground:fde=unused:spb=units:i=1212:kws=inv_arity:rawr=on:av=off:newcnf=on:erd=off:gsp=on:bsr=unit_only:plsq=on:plsqr=52,371_0");
    feqAtomsL180propNZatomsG50.push("ott-1011_45995:1048576_anc=none:to=lpo:sil=4000:tgt=ground:fde=unused:sp=const_frequency:lma=on:spb=goal_then_units:acc=model:lcm=predicate:nwc=0.310817:avsq=on:cond=on:i=2431:avsqr=21767,262144:nm=3:ins=1:uhcvi=on:bsr=unit_only:afr=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+34_1:128_sil=2000:tgt=full:fde=unused:sp=unary_first:sos=on:lcm=predicate:i=1296:sd=1:bd=off:av=off:ss=axioms:sgt=8_0");
    feqAtomsL180propNZatomsG50.push("lrs+21_3:1_to=lpo:drc=encompass:sil=32000:spb=intro:flr=on:updr=off:i=2643:anc=all:bsd=on:fd=preordered:fsd=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_16:1_to=lpo:sil=2000:sos=on:spb=intro:st=2.0:i=1421:sd=2:afp=50:bd=off:nm=6:sup=off:afq=2.0:ss=axioms:ins=1:fs=off:fsr=off:alpa=true_0");
    feqAtomsL180propNZatomsG50.push("dis+1011_4_add=large:amm=off:sims=off:sac=on:sp=frequency:tgt=ground:i=1580_0");
    feqAtomsL180propNZatomsG50.push("dis+1011_1:20_anc=none:sil=2000:tgt=ground:bce=on:s2agt=16:newcnf=on:i=1730:kws=precedence:slsq=on:slsqc=3:slsqr=1,4_0");
    feqAtomsL180propNZatomsG50.push("lrs+1011_10195:1048576_to=lpo:sil=2000:fde=none:ile=on:sp=const_frequency:lma=on:lcm=reverse:nwc=22.1777:flr=on:st=1.5:i=1994:bs=on:sd=2:awrs=converge:awrsf=457:bd=preordered:nm=5:fsd=on:ss=axioms:sgt=20:rawr=on:etr=on:bsd=on:afp=10:afq=2.1644398980198307_0");
    feqAtomsL180propNZatomsG50.push("dis-1010_1:2_bsr=unit_only:sil=32000:tgt=full:i=2027:nm=16:bd=off_0");
    feqAtomsL180propNZatomsG50.push("lrs-1010_1:3_sil=4000:tgt=ground:sos=on:i=3991:nm=3:ss=axioms:nwc=2.0_0");
    feqAtomsL180propNZatomsG50.push("lrs+1010_1:2_sil=4000:tgt=ground:nwc=10.0:st=2.0:i=2059:sd=1:bd=off:ss=axioms_0");
    feqAtomsL180propNZatomsG50.push("lrs+2_1:1_sil=2000:sos=all:st=5.0:i=2247:bd=off:av=off:ss=axioms:sd=2:sup=off_0");
    feqAtomsL180propNZatomsG50.push("lrs+1002_1:1_slsqr=2,1:sil=16000:urr=full:bce=on:nwc=2.0:slsq=on:st=5.0:i=2265:sd=2:ss=axioms_0");
    feqAtomsL180propNZatomsG50.push("lrs-10_1:2_to=lpo:drc=encompass:sil=4000:sp=weighted_frequency:rp=on:flr=on:slsq=on:s2a=on:i=2268:av=off:rawr=on:fdi=1_0");
    feqAtomsL180propNZatomsG50.push("lrs+11_1:1024_bsr=unit_only:drc=off:sil=4000:sp=unary_frequency:urr=ec_only:fd=preordered:gs=on:i=2862:kws=inv_arity_squared:av=off:fsr=off:nwc=10.0_0");
    feqAtomsL180propNZatomsG50.push("lrs-1010_18:13_to=lpo:tgt=full:sos=all:avsqc=1:avsq=on:i=3175:avsqr=19,49:ss=axioms:sgt=32:rawr=on:nwc=3.0:sil=32000_0");
    feqAtomsL180propNZatomsG50.push("lrs-1010_552419:524288_sfv=off:slsqr=21968697,524288:to=lpo:drc=off:plsq=on:plsqr=95593,524288:sp=frequency:rp=on:flr=on:slsq=on:i=3255:rawr=on:sil=16000_0");
    feqAtomsL180propNZatomsG50.push("lrs+1010_1:102_sil=4000:nwc=11.034643852242374:i=3568:nm=2:ile=on:fd=off:ss=axioms:st=5.0:to=lpo_0");
    feqAtomsL180propNZatomsG50.push("lrs+11_1:1024_to=lpo:drc=off:sil=16000:tgt=full:sp=const_frequency:spb=intro:i=3720:awrs=converge:bd=preordered:av=off:rawr=on_0");
    feqAtomsL180propNZatomsG50.push("dis+21_3:17_i=4535:kws=inv_frequency:slsq=on:slsql=off:slsqc=1:slsqr=247,761:s2agt=8:rawr=on:amm=off:fsr=off:awrs=converge:awrsf=283:uhcvi=on:sil=256000_0");
    feqAtomsL180propNZatomsG50.push("dis+1010_1:4_tgt=ground:sp=weighted_frequency:spb=goal_then_units:br=off:i=6294:sd=1:nm=16:ins=4:av=off:fsd=on:ss=axioms:sgt=32:sil=128000:sims=off:flr=on:nwc=3.0_0");
    feqAtomsL180propNZatomsG50.push("dis+11_1:9_drc=off:sil=32000:tgt=ground:sp=reverse_frequency:abs=on:st=-1.0:i=7070:kws=precedence:bd=off:fsr=off:amm=off:ss=included_0");
    feqAtomsL180propNZatomsG50.push("lrs+2_1:32_drc=off:sil=16000:tgt=ground:sp=const_frequency:st=5.0:i=7115:ss=axioms:bd=preordered:to=lpo_0");
    feqAtomsL180propNZatomsG50.push("lrs+11_1:64_bsr=unit_only:sil=16000:tgt=full:plsq=on:spb=goal_then_units:i=8565:ins=6:ss=axioms:sgt=32:rawr=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+10_1:32_bsr=unit_only:drc=off:sil=32000:sp=const_frequency:flr=on:slsq=on:i=8717:bs=on:kws=precedence:sac=on:nicw=on_0");
    feqAtomsL180propNZatomsG50.push("lrs-1003_1:14_sil=256000:tgt=full:sp=unary_first:newcnf=on:s2a=on:i=17715:kws=inv_frequency:bd=off:uhcvi=on:rawr=on:sac=on_0");
    feqAtomsL180propNZatomsG50.push("lrs-1011_271883:1048576_slsqr=2858345,1048576:to=lpo:sil=128000:sp=frequency:gs=on:flr=on:slsq=on:i=9724:awrs=decay:slsql=off:awrsf=90:fsr=off:ss=axioms:sgt=32:bsr=unit_only_0");
    feqAtomsL180propNZatomsG50.push("dis-1004_2_av=off:fsd=off:gsp=on:nm=4:nwc=1.5:sp=reverse_frequency:tgt=ground:i=15904_0");
    feqAtomsL180propNZatomsG50.push("dis+1002_1:1_tgt=ground:sos=on:i=16287:urr=full:sil=128000:si=on:rtra=on:nm=32:ile=on:bs=on:sp=reverse_arity:add=large:ss=axioms:st=2.0:erd=off:lma=on:etr=on_0");
    feqAtomsL180propNZatomsG50.push("lrs-1010_2_av=off:bce=on:cond=on:er=filter:fde=unused:lcm=predicate:nm=2:nwc=3.0:sims=off:sp=frequency:urr=on:sil=256000:i=42157_0");
    feqAtomsL180propNZatomsG50.push("dis+4_1:13_to=lpo:drc=off:sil=64000:bsd=on:sp=weighted_frequency:flr=on:cond=on:i=23291:rawr=on:av=off:fsd=on_0");
    feqAtomsL180propNZatomsG50.push("lrs+21_9739:1048576_drc=off:sil=128000:tgt=ground:spb=non_intro:s2a=on:i=25831:s2at=2.0:kws=precedence:sp=reverse_arity:awrs=decay:awrsf=270_0");
    feqAtomsL180propNZatomsG50.push("lrs+21_1:6_to=lpo:drc=off:sil=64000:tgt=ground:fd=preordered:i=28283_0");
    feqAtomsL180propNZatomsG50.push("lrs+2_5:4_anc=none:br=off:fde=unused:gsp=on:nm=32:nwc=1.3:sims=off:sos=all:urr=on:sil=128000:i=62728_0");

    // total_instr 714368
    // len(covered) 1134

    Schedule feqAtomsL180propNZtiny;

    feqAtomsL180propNZtiny.push("ott+4_40_av=off:bce=on:fsd=off:fde=unused:nm=4:nwc=1.1:sos=all:sp=frequency:i=69040_0");
    feqAtomsL180propNZtiny.push("lrs+1011_8:1_sil=128000:tgt=ground:fde=unused:sp=frequency:nwc=5.0:lwlo=on:i=105338:awrs=converge:awrsf=1385:av=off_0");
    feqAtomsL180propNZtiny.push("dis+1011_1:99_anc=none:fde=unused:plsqc=2:bsd=on:plsq=on:plsqr=109,504:sp=reverse_frequency:spb=intro:rp=on:alpa=random:s2a=on:i=257151:s2at=-1.0:aac=none:nm=16:rawr=on:sil=256000:acc=model_0");

    feqAtomsL180propNZtiny.push("lrs+21_2461:262144_anc=none:drc=off:sil=2000:sp=occurrence:nwc=6.0:updr=off:st=3.0:i=109:sd=2:afp=4000:erml=3:nm=14:afq=2.0:uhcvi=on:ss=included:er=filter:abs=on:nicw=on:ile=on:sims=off:s2a=on:s2agt=50:s2at=-1.0:plsq=on:plsql=on:plsqc=2:plsqr=1,32:newcnf=on:bd=off:to=lpo_0");
    feqAtomsL180propNZtiny.push("lrs-1011_37821:262144_bsr=unit_only:sil=2000:fde=none:plsq=on:plsqr=43543,131072:bce=on:rnwc=on:plsql=on:rp=on:nwc=10.0:newcnf=on:i=109:awrs=decay:awrsf=10:ep=R:mep=off:amm=sco_0");
    feqAtomsL180propNZtiny.push("ott-1011_16:1_sil=2000:sp=const_max:urr=on:lsd=20:st=3.0:i=117:ss=axioms:gsp=on:rp=on:sos=on:fd=off:aac=none_0");
    feqAtomsL180propNZtiny.push("lrs+1010_1:1_to=lpo:sil=2000:sos=on:fd=off:i=117:bd=off_0");
    feqAtomsL180propNZtiny.push("lrs+21_1:64_drc=encompass:sil=32000:bsd=on:lma=on:spb=goal:nwc=10.0:i=123:add=large:ss=axioms:sgt=16:irw=on_0");
    feqAtomsL180propNZtiny.push("lrs+2_1:1_sil=16000:fde=none:sos=all:nwc=5.0:i=117:ep=RS:s2pl=on:lma=on:afp=100000_0");
    feqAtomsL180propNZtiny.push("lrs+1011_1:12_anc=none:drc=off:sil=64000:sims=off:sp=unary_first:spb=goal_then_units:lsd=20:rnwc=on:nwc=2.0:i=138:add=off:awrs=converge:bd=off:uhcvi=on:tgt=ground:afp=300:afq=1.63_0");
    feqAtomsL180propNZtiny.push("dis+2_1:28_anc=none:sil=2000:plsqc=1:plsq=on:plsqr=87,4:sp=unary_first:spb=intro:plsql=on:st=2.0:i=117:afp=10:bd=off:nm=16:afr=on:ss=axioms:to=lpo:cond=fast:fsr=off:nwc=7.0_0");
    feqAtomsL180propNZtiny.push("lrs+1011_1:4_to=lpo:sil=4000:plsq=on:plsqr=32,1:sp=reverse_frequency:fs=off:spb=goal:plsql=on:rp=on:i=108:nm=16:fsr=off:amm=off:rawr=on:drc=off:avsq=on:avsql=on:avsqr=31485,524288:plsqc=2:nwc=5.0_0");
    feqAtomsL180propNZtiny.push("lrs-1002_1:1024_anc=none:slsqr=6559637,262144:sil=256000:tgt=ground:fde=unused:bsd=on:sp=const_min:sos=on:bce=on:rp=on:slsqc=3:slsq=on:cond=on:s2a=on:i=109:s2at=3.5:sd=3:kws=inv_arity:afp=300:slsql=off:bsdmm=3:afq=3.34235:uhcvi=on:ss=axioms:rawr=on:add=large:acc=model_0");
    feqAtomsL180propNZtiny.push("lrs+11_1:1_sos=on:urr=on:s2a=on:i=124:sd=1:aac=none:ss=axioms:gsp=on:sil=128000:nm=3:bce=on:fd=preordered:alpa=true:etr=on:bd=off:lcm=predicate_0");
    feqAtomsL180propNZtiny.push("lrs-1_1:1_drc=off:sil=4000:tgt=full:sp=occurrence:sos=on:urr=on:rp=on:i=247:bs=on:ins=1:av=off:rawr=on:to=lpo:br=off_0");
    feqAtomsL180propNZtiny.push("lrs+21_1:6_to=lpo:drc=off:sil=64000:tgt=ground:fd=preordered:i=151_0");
    feqAtomsL180propNZtiny.push("lrs+1011_1:32_sil=2000:tgt=ground:acc=model:lsd=10:nwc=1.1:flr=on:s2pl=no:i=113:bd=off:gsp=on:rawr=on_0");
    feqAtomsL180propNZtiny.push("dis+1010_5:1_sil=64000:sp=const_min:sos=on:acc=model:i=120:kws=precedence:bd=off:nm=20:alpa=random:ss=axioms_0");
    feqAtomsL180propNZtiny.push("dis+1002_1:128_sil=2000:fde=none:i=145:plsq=on:plsqc=1:plsqr=6,1:bd=off:tgt=ground:sac=on:sfv=off:s2a=on:s2at=5.0_0");
    feqAtomsL180propNZtiny.push("lrs+1010_974213:1048576_nwc=9.0:s2a=on:i=123:bd=off:lwlo=on:fd=off:sil=256000:s2agt=10:sims=off:nm=9:sp=const_min:rp=on:er=known:cond=fast:bce=on:abs=on:irw=on:amm=sco:afp=2000:updr=off:add=off:to=lpo:awrs=decay:awrsf=260:rawr=on:afq=2.0:uhcvi=on_0");
    feqAtomsL180propNZtiny.push("dis+11_1:7_sil=2000:tgt=ground:sp=reverse_arity:i=851:fd=preordered:fsr=off:drc=encompass_0");
    feqAtomsL180propNZtiny.push("lrs-21_1:1_to=lpo:sil=2000:sp=frequency:sos=on:lma=on:i=126:sd=2:ss=axioms:ep=R_0");
    feqAtomsL180propNZtiny.push("lrs+1010_1:16_sil=2000:plsq=on:plsqr=32,1:slsq=on:i=138:slsql=off:bd=off:er=filter:erml=3:slsqc=2:cond=on:alpa=false:fsr=off:acc=on_0");
    feqAtomsL180propNZtiny.push("lrs+1011_1:6_to=lpo:drc=encompass:sil=256000:tgt=full:sp=unary_first:nwc=10.0:i=1458:aac=none:bd=preordered:ss=axioms:sgt=16_0");
    feqAtomsL180propNZtiny.push("dis+1011_2809:262144_drc=off:sil=2000:tgt=ground:plsq=on:plsqr=450601,524288:sp=reverse_arity:sos=on:foolp=on:rnwc=on:plsql=on:fd=preordered:rp=on:nwc=4.574864195731069:i=172:bd=preordered:nm=6:fsr=off:ss=axioms:sgt=100:rawr=on:afp=1000:afq=2.7331722210582745_0");
    feqAtomsL180propNZtiny.push("lrs+21_1:334_sil=64000:sp=frequency:spb=units:nwc=5.0:flr=on:s2a=on:i=246:s2at=3.0:bd=off:uhcvi=on:abs=on:alpa=true:lcm=predicate_0");
    feqAtomsL180propNZtiny.push("lrs-32_1:4_to=lpo:drc=off:sil=2000:sp=reverse_arity:spb=goal_then_units:urr=on:nwc=2.0:i=480:ss=included:st=2.0:bd=preordered_0");
    feqAtomsL180propNZtiny.push("lrs-1011_1:1_sil=4000:plsq=on:plsqr=32,1:sp=frequency:plsql=on:nwc=10.0:i=266:aac=none:afr=on:ss=axioms:er=filter:sgt=16:rawr=on:etr=on:lma=on_0");
    feqAtomsL180propNZtiny.push("lrs+1010_1:128_sil=2000:tgt=ground:nwc=2.4:flr=on:i=185:bd=off:ins=2:av=off:rawr=on:plsq=on:plsql=on:plsqc=1:plsqr=1947,254:rnwc=on_0");
    feqAtomsL180propNZtiny.push("lrs+2_1:1_to=lpo:drc=off:sil=4000:tgt=ground:sp=unary_first:spb=non_intro:urr=on:fd=preordered:i=1687:afp=1000:ins=3:rawr=on_0");
    feqAtomsL180propNZtiny.push("lrs+1011_1:2_to=lpo:drc=off:sil=2000:sp=const_min:urr=on:lcm=predicate:nwc=16.7073:updr=off:newcnf=on:i=207:av=off:rawr=on:ss=included:st=5.0:erd=off:flr=on_0");
    feqAtomsL180propNZtiny.push("lrs+1002_1:4_sil=2000:fde=unused:plsq=on:plsqr=32,1:sos=on:bce=on:i=208:sd=1:ss=included:rawr=on_0");
    feqAtomsL180propNZtiny.push("ott+33_191939:1048576_drc=encompass:sil=4000:tgt=ground:sp=const_frequency:lma=on:spb=goal:gs=on:nwc=17.8226:gsem=off:cond=fast:i=502:kws=inv_arity:bd=preordered:nm=35:av=off:fsr=off:uhcvi=on:rawr=on:bs=unit_only:urr=ec_only:ins=1_0");
    feqAtomsL180propNZtiny.push("lrs+1002_74:59_drc=off:tgt=full:sos=all:cond=fast:i=234:kws=inv_frequency:afp=300:afq=2.0744697298148953:rawr=on:urr=full:sil=128000:si=on:rtra=on:random_seed=3250543_0");
    feqAtomsL180propNZtiny.push("dis-1011_1785:1048576_bsr=unit_only:sil=4000:tgt=ground:plsqc=1:plsq=on:plsqr=125493,524288:sp=frequency:spb=goal:plsql=on:nwc=2.32086:updr=off:newcnf=on:cond=fast:st=2:s2a=on:i=253:s2at=4:bd=off:nm=3:ins=3:aer=off:uhcvi=on:afr=on:ss=axioms:sgt=20:rawr=on:fsr=off_0");
    feqAtomsL180propNZtiny.push("lrs+11_3:4_drc=off:sil=2000:tgt=ground:sp=occurrence:urr=on:nwc=5.0:st=3.0:i=327:kws=inv_frequency:av=off:ss=axioms:br=off:rawr=on:newcnf=on_0");
    feqAtomsL180propNZtiny.push("lrs-32_2:11_drc=encompass:sil=4000:sp=reverse_frequency:nwc=10.0:s2a=on:i=1751:s2at=5.0:nm=16:amm=sco_0");
    feqAtomsL180propNZtiny.push("dis+1011_1:24_drc=off:sil=4000:tgt=full:spb=goal:fd=preordered:avsq=on:i=347:fsr=off:rawr=on_0");
    feqAtomsL180propNZtiny.push("lrs+1002_1:7_to=lpo:drc=encompass:sil=2000:tgt=full:sp=reverse_arity:spb=non_intro:fd=preordered:nwc=10.0:st=3.0:i=598:ins=2:ss=axioms_0");
    feqAtomsL180propNZtiny.push("lrs+10_1:3_drc=off:sil=256000:sp=unary_first:lwlo=on:i=647:kws=precedence:ins=3:rawr=on:nwc=10.0_0");
    feqAtomsL180propNZtiny.push("dis+1011_3:8_bsr=unit_only:slsqr=1,16:sil=2000:plsq=on:plsqr=296,127:sp=reverse_frequency:lsd=5:nwc=10.0:slsqc=3:slsq=on:st=3.0:i=649:s2at=4.5:sd=4:slsql=off:nm=16:ins=5:ss=axioms:sgt=20:rawr=on:urr=ec_only:to=lpo_0");
    feqAtomsL180propNZtiny.push("dis+1011_986949:1048576_sil=2000:irw=on:fde=none:ile=on:etr=on:sp=unary_first:bce=on:fd=preordered:rp=on:nwc=22.6584:cond=fast:st=2.5:s2pl=on:i=492:s2at=2:sd=7:kws=precedence:nm=0:ins=1:av=off:gsp=on:ss=axioms:rawr=on:gs=on:lsd=20_0");
    feqAtomsL180propNZtiny.push("lrs+2_1:1024_sil=2000:sos=all:urr=on:br=off:i=656:nm=2:updr=off:gsp=on_0");
    feqAtomsL180propNZtiny.push("dis+1011_1:1_sil=4000:tgt=full:newcnf=on:i=715:sd=2:ss=axioms:sgt=16:rawr=on:fsr=off_0");
    feqAtomsL180propNZtiny.push("dis+11_1:1024_sil=2000:tgt=ground:i=1463:awrs=converge:fd=preordered_0");
    feqAtomsL180propNZtiny.push("dis+10_5375:524288_to=lpo:drc=off:sil=2000:tgt=ground:plsq=on:plsqr=2270675,65536:sp=const_min:foolp=on:spb=goal_then_units:urr=ec_only:lcm=reverse:fd=preordered:nwc=1.91851:nicw=on:s2a=on:i=869:s2at=1.5:add=off:nm=16:rawr=on_0");
    feqAtomsL180propNZtiny.push("lrs+11_5:2_to=lpo:drc=encompass:sil=8000:tgt=full:sp=const_frequency:sos=all:lma=on:spb=goal_then_units:nwc=10.0:i=1705:fsr=off:rawr=on:fdi=5_0");
    feqAtomsL180propNZtiny.push("lrs+2_1:128_drc=encompass:sil=32000:tgt=full:sp=unary_frequency:spb=non_intro:nwc=3.0:st=5.0:s2a=on:i=12192:s2at=5.0:kws=precedence:bd=preordered:ss=included:awrs=converge:awrsf=90_0");
    feqAtomsL180propNZtiny.push("lrs+11_7:12_sil=2000:sp=occurrence:sos=on:erd=off:lcm=reverse:gs=on:st=5.0:i=1335:awrs=converge:bd=off:ss=axioms:fs=off:fsr=off:rawr=on_0");
    feqAtomsL180propNZtiny.push("lrs+2_1:7_drc=encompass:sil=64000:tgt=full:sp=reverse_arity:i=54422:ins=6:rawr=on:kws=inv_frequency:fde=unused:slsq=on:slsqr=7,8_0");
    feqAtomsL180propNZtiny.push("lrs+1011_1:1_drc=encompass:sil=128000:tgt=ground:i=30639:kws=frequency:ss=axioms:lwlo=on:fde=unused:sp=reverse_arity_0");
    feqAtomsL180propNZtiny.push("lrs+10_2:7_bsr=unit_only:drc=off:sil=16000:sos=on:abs=on:fd=preordered:nicw=on:i=13991:uhcvi=on:rawr=on:nwc=0.8650794518795772_0");
    feqAtomsL180propNZtiny.push("ott+11_1:32_sil=64000:tgt=full:sp=const_max:spb=units:slsqc=1:slsq=on:st=5.0:i=18307:s2at=5.0:sd=1:kws=precedence:ss=axioms_0");
    feqAtomsL180propNZtiny.push("lrs+2_1:3_drc=encompass:sil=128000:tgt=full:sp=frequency:s2a=on:i=125595:kws=precedence:bd=preordered:ins=11:lwlo=on:s2at=1.5:ss=included:sgt=8:awrs=converge_0");
    feqAtomsL180propNZtiny.push("dis+2_1:5_slsqr=331891,1048576:to=lpo:sil=128000:tgt=ground:sp=unary_first:spb=goal_then_units:s2agt=8:slsq=on:i=23437:awrs=converge:awrsf=1398:slsqc=4:plsq=on:plsql=on:plsqc=1:plsqr=5650705,131072_0");
    feqAtomsL180propNZtiny.push("lrs+35_1:1_to=lpo:sil=128000:tgt=full:fd=preordered:lwlo=on:i=73025:bd=preordered:drc=off:av=off_0");
    feqAtomsL180propNZtiny.push("lrs-4_1:24_slsqr=493885,1048576:drc=encompass:sil=128000:tgt=full:sp=weighted_frequency:fd=preordered:flr=on:slsq=on:i=113200:bs=unit_only:av=off:fsr=off:rawr=on_0");
    feqAtomsL180propNZtiny.push("lrs+1011_1:1_drc=off:sil=128000:tgt=ground:sos=on:rnwc=on:rp=on:nwc=10.0:nicw=on:i=96173:nm=2:cond=on:bd=off_0");

    // total_instr 1013264
    // len(covered) 673

    if (cat == Property::FNE) {
      quick = std::move(fne);

      fallback.loadFromIterator(feqAtomsG18000.iterFifo());
      fallback.loadFromIterator(feqAtomsG2800.iterFifo());
      fallback.loadFromIterator(feqAtomsG180.iterFifo());
      fallback.loadFromIterator(feqAtomsL180propZ.iterFifo());
      fallback.loadFromIterator(feqAtomsL180propNZatomsG50.iterFifo());
      fallback.loadFromIterator(feqAtomsL180propNZtiny.iterFifo());

    } else if (atoms > 18000) {
      quick = std::move(feqAtomsG18000);

      fallback.loadFromIterator(fne.iterFifo());
      fallback.loadFromIterator(feqAtomsG2800.iterFifo());
      fallback.loadFromIterator(feqAtomsG180.iterFifo());
      fallback.loadFromIterator(feqAtomsL180propZ.iterFifo());
      fallback.loadFromIterator(feqAtomsL180propNZatomsG50.iterFifo());
      fallback.loadFromIterator(feqAtomsL180propNZtiny.iterFifo());

    } else if (atoms > 2800) {
      quick = std::move(feqAtomsG2800);

      fallback.loadFromIterator(feqAtomsG18000.iterFifo());
      fallback.loadFromIterator(feqAtomsG180.iterFifo());
      fallback.loadFromIterator(fne.iterFifo());
      fallback.loadFromIterator(feqAtomsL180propZ.iterFifo());
      fallback.loadFromIterator(feqAtomsL180propNZatomsG50.iterFifo());
      fallback.loadFromIterator(feqAtomsL180propNZtiny.iterFifo());

    } else if (atoms > 180) {
      quick = std::move(feqAtomsG180);

      fallback.loadFromIterator(feqAtomsG2800.iterFifo());
      fallback.loadFromIterator(feqAtomsL180propZ.iterFifo());
      fallback.loadFromIterator(feqAtomsG18000.iterFifo());
      fallback.loadFromIterator(feqAtomsL180propNZatomsG50.iterFifo());
      fallback.loadFromIterator(feqAtomsL180propNZtiny.iterFifo());
      fallback.loadFromIterator(fne.iterFifo());

    } else if (props == 0) {
      quick = std::move(feqAtomsL180propZ);

      fallback.loadFromIterator(feqAtomsL180propNZatomsG50.iterFifo());
      fallback.loadFromIterator(feqAtomsG180.iterFifo());
      fallback.loadFromIterator(feqAtomsL180propNZtiny.iterFifo());
      fallback.loadFromIterator(feqAtomsG2800.iterFifo());
      fallback.loadFromIterator(feqAtomsG18000.iterFifo());
      fallback.loadFromIterator(fne.iterFifo());

    } else if (atoms > 50) {
      quick = std::move(feqAtomsL180propNZatomsG50);

      fallback.loadFromIterator(feqAtomsL180propNZtiny.iterFifo());
      fallback.loadFromIterator(feqAtomsL180propZ.iterFifo());
      fallback.loadFromIterator(feqAtomsG180.iterFifo());
      fallback.loadFromIterator(feqAtomsG2800.iterFifo());
      fallback.loadFromIterator(feqAtomsG18000.iterFifo());
      fallback.loadFromIterator(fne.iterFifo());

    } else {
      quick = std::move(feqAtomsL180propNZtiny);

      fallback.loadFromIterator(feqAtomsL180propNZatomsG50.iterFifo());
      fallback.loadFromIterator(feqAtomsL180propZ.iterFifo());
      fallback.loadFromIterator(feqAtomsG180.iterFifo());
      fallback.loadFromIterator(feqAtomsG2800.iterFifo());
      fallback.loadFromIterator(feqAtomsG18000.iterFifo());
      fallback.loadFromIterator(fne.iterFifo());
    }
  }
}

void Schedules::getCascSat2024Schedule(const Property& property, Schedule& quick, Schedule& fallback)
{
  // The TFN division: Typed (monomorphic) First-order Non-theorems (axioms with a countersatisfiable conjecture, and satisfiable axiom sets).

  quick.push("fmb+10_1:1_sil=256000:i=98885:tgt=full:fmbsr=1.3:fmbss=10_0");
  quick.push("ott+10_10:1_add=off:afr=on:amm=off:anc=all:bd=off:bs=on:fsr=off:irw=on:lma=on:msp=off:nm=4:nwc=4.0:sac=on:sp=reverse_frequency:i=99418_0");
  quick.push("fmb+10_1:1_sil=256000:fmbes=contour:i=214858:bce=on_0");
  quick.push("fmb+10_1:1_sil=256000:fmbss=23:fmbes=contour:newcnf=on:fmbsr=1.14:i=152523:nm=2:gsp=on:rp=on_0");

  quick.push("ott+21_1:1_sil=4000:i=104:fsd=on:fd=off:newcnf=on_0");
  quick.push("ott+11_8:59_sil=16000:sp=occurrence:lsd=20:abs=on:i=146:aac=none:nm=16:fdi=10:rawr=on:nicw=on_0");
  quick.push("ott-4_1:1_sil=4000:sp=reverse_arity:lcm=predicate:newcnf=on:i=115:bce=on:fd=off:fs=off:fsr=off_0");
  quick.push("dis+11_1:3_bsr=unit_only:sil=2000:rp=on:newcnf=on:i=404:kws=precedence:lsd=100_0");
  quick.push("ott-21_1:1_sil=4000:sp=const_frequency:i=175:fsr=off:fs=off:av=off_0");
  quick.push("ott+33_1:1_to=lpo:sil=8000:sp=weighted_frequency:rp=on:i=270:nm=3:fsr=off:sac=on_0");
  quick.push("ott+4_1:1_sil=2000:i=900:bd=off:fsr=off_0");
  quick.push("fmb+10_1:1_sil=8000:fde=unused:fmbes=contour:i=7859:nm=2:fmbswr=0_0");
  quick.push("ott+11_1:2_anc=none:sil=2000:sp=const_max:spb=units:s2a=on:i=2145:s2at=5.0:awrs=converge:awrsf=170:rawr=on:gs=on:fsr=off_0");
  quick.push("ott-30_1:1024_sil=4000:alpa=true:newcnf=on:i=1187:bs=unit_only:ins=1:amm=off_0");
  quick.push("fmb+10_1:1_sil=32000:i=23580:newcnf=on_0");
  quick.push("fmb+10_1:1_sil=32000:fmbss=17:fmbsr=2.0:i=2892_0");
  quick.push("ott-10_1:1_sil=4000:i=1693_0");
  quick.push("dis+21_1:1_sil=4000:gs=on:sac=on:newcnf=on:gsem=off:i=1735:gsaa=full_model:abs=on:anc=none_0");
  quick.push("fmb+10_1:1_fmbas=expand:sil=128000:i=131798:nm=2:fmbksg=on:fmbss=4:fmbsr=1.77:rp=on_0");
  quick.push("fmb+10_1:1_sil=16000:fmbss=16:i=3451:newcnf=on_0");
  quick.push("ott+11_1:64_sil=4000:rp=on:i=3978:bd=off:fsr=off_0");
  quick.push("dis+35_1:64_to=lpo:sil=32000:sp=occurrence:urr=on:sac=on:i=33091:fsr=off_0");
  quick.push("dis-4_1:1_sil=16000:sp=const_frequency:sac=on:newcnf=on:i=9564_0");
  quick.push("fmb+10_1:1_sil=64000:i=50409:nm=2:gsp=on_0");
  quick.push("dis+2_3:1_bsr=on:sil=64000:abs=on:i=10852:gsp=on:fs=off:fsr=off_0");
  quick.push("dis+11_61:31_bsr=unit_only:sil=16000:sp=frequency:rp=on:newcnf=on:i=11327:uhcvi=on:rawr=on:abs=on:lsd=5:add=off_0");
  quick.push("fmb+10_1:1_fmbas=expand:sil=128000:i=17908:nm=2:fmbss=15:gsp=on_0");
  quick.push("dis+11_1:1_anc=all:sil=64000:rp=on:newcnf=on:i=22636:alpa=false:atotf=0.1:gs=on_0");
  quick.push("fmb+10_1:1_i=30223_0");
  quick.push("ott+11_8:1_sil=64000:i=37350:fsr=off:bsr=unit_only:newcnf=on_0");
  quick.push("dis-2_2:3_amm=sco:anc=none:bce=on:fsr=off:gsp=on:nm=16:nwc=1.2:nicw=on:sac=on:sp=weighted_frequency:i=80557_0");
  quick.push("fmb+10_1:1_sil=128000:fmbss=21:newcnf=on:i=44200:gsp=on_0");
  quick.push("dis+2_11_add=large:afr=on:amm=off:bd=off:bce=on:fsd=off:fde=none:gs=on:gsaa=full_model:gsem=off:irw=on:msp=off:nm=4:nwc=1.3:sas=z3:sims=off:sac=on:sp=reverse_arity:i=55207_0");
  quick.push("dis+1_20_av=off:lcm=predicate:nm=2:nwc=2.0:i=81447_0");
  quick.push("ott+4_64_acc=on:anc=none:bs=on:bsr=on:fsd=off:gs=on:gsem=off:irw=on:msp=off:nwc=2.5:nicw=on:sims=off:i=93915_0");

  //total_instr 1326802
  // len(covered) 1067
}
