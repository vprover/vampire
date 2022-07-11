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

#include "Schedules.hpp"

#include "Shell/Options.hpp"

#include <fstream>

using namespace Lib;
using namespace Shell;
using namespace CASC;

void Schedules::getScheduleFromFile(const vstring& filename, Schedule& quick)
{
  if (filename == "") {
    USER_ERROR("Schedule file was not set.");
  }
  BYPASSING_ALLOCATOR;
  ifstream schedule_file (filename.c_str());
  if (schedule_file.fail()) {
    USER_ERROR("Cannot open schedule file: " + filename);
  }
  ASS(schedule_file.is_open());
  vstring line;
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
      quick.push("ins+10_1_av=off:bce=on:cond=on:fde=unused:gsp=on:igbrr=0.7:igrr=32/1:igrp=700:igrpq=2.0:igs=1010:igwr=on:lcm=reverse:nwc=1:ss=axioms:st=3.0:sos=theory:urr=on:uhcvi=on_139");
    }
    else if (atoms < 2000) {
      quick.push("ott+10_64_add=off:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:lcm=predicate:lma=on:nwc=1:sac=on:sp=reverse_arity:urr=on_47");
      quick.push("ins+10_1_av=off:igbrr=0.2:igpr=on:igrp=400:igrpq=2.0:igs=1:nwc=2.5:sos=theory_283");
      quick.push("lrs+2_64_add=large:afp=40000:afq=1.1:bd=off:bs=on:bsr=on:bce=on:fde=unused:irw=on:lma=on:lwlo=on:nwc=1:stl=30:uhcvi=on_25");
      quick.push("lrs+1011_14_afr=on:afp=100000:afq=1.1:anc=none:bd=off:bsr=on:irw=on:nwc=1:sas=z3:stl=30_90");
      quick.push("lrs+1003_10_afp=4000:afq=1.2:amm=sco:anc=none:bd=off:bsr=on:br=off:bce=on:fde=unused:lma=on:nwc=1:nicw=on:stl=120:sac=on:urr=on:updr=off:uhcvi=on_417");
      quick.push("ins+11_128_av=off:cond=on:fsr=off:irw=on:igbrr=0.5:igpr=on:igrr=1/2:igrp=2000:igrpq=1.5:igs=1010:igwr=on:lma=on:nwc=1:sos=all:sp=occurrence:updr=off_194");
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
    fallback.push("ins+10_1_av=off:igbrr=0.2:igpr=on:igrp=400:igrpq=2.0:igs=1:nwc=2.5:sos=theory_300");
    fallback.push("lrs+2_64_add=large:afp=40000:afq=1.1:bd=off:bs=on:bsr=on:bce=on:fde=unused:irw=on:lma=on:lwlo=on:nwc=1:uhcvi=on_300");
    fallback.push("dis+4_5_afp=1000:afq=1.1:amm=off:anc=none:bd=off:gs=on:irw=on:lcm=predicate:lma=on:nwc=1:sas=z3:sos=all:sp=occurrence_300");
    fallback.push("lrs+1003_10_afp=4000:afq=1.2:amm=sco:anc=none:bd=off:bsr=on:br=off:bce=on:fde=unused:lma=on:nwc=1:nicw=on:sac=on:urr=on:updr=off:uhcvi=on_1200");
    fallback.push("dis+11_2:3_add=large:afp=10000:afq=1.2:anc=none:bd=off:bce=on:cond=fast:er=filter:fsr=off:fde=unused:gsp=on:nwc=5:sos=theory:sac=on:urr=on_300");
    fallback.push("ott-4_6_add=off:afr=on:afp=100000:afq=1.4:amm=sco:bs=on:fde=unused:gs=on:gsaa=full_model:gsem=on:irw=on:nwc=1:sas=z3:sac=on:updr=off:uhcvi=on_600");
    fallback.push("ott+11_50_aac=none:add=off:afp=1000:afq=1.4:anc=none:bs=unit_only:fde=none:gs=on:gsem=off:lma=on:nwc=1:sas=z3:sac=on:uhcvi=on_200");
    fallback.push("dis-11_32_av=off:bs=unit_only:gs=on:irw=on:lma=on:nwc=1:updr=off_300");
    fallback.push("ins+10_1_av=off:bce=on:cond=on:fde=unused:gsp=on:igbrr=0.7:igrr=32/1:igrp=700:igrpq=2.0:igs=1010:igwr=on:lcm=reverse:nwc=1:ss=axioms:st=3.0:sos=theory:urr=on:uhcvi=on_300");
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
      quick.push("ins+11_3_av=off:irw=on:igbrr=0.1:igpr=on:igrr=1/8:igrp=1400:igrpq=1.3:igs=1002:igwr=on:lcm=predicate:lma=on:nm=16:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:sp=reverse_arity_49");
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
      quick.push("ins+11_8_av=off:cond=fast:fde=none:gsp=on:irw=on:igbrr=0.2:igpr=on:igrr=1/8:igrp=200:igrpq=1.1:igs=1010:igwr=on:lcm=predicate:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=on:sp=occurrence:uhcvi=on_40");
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
      quick.push("ins+11_3_av=off:irw=on:igbrr=0.1:igpr=on:igrr=1/8:igrp=1400:igrpq=1.3:igs=1002:igwr=on:lcm=predicate:lma=on:nm=16:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:sp=reverse_arity_20");
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
      quick.push("ins+11_3_av=off:irw=on:igbrr=0.1:igpr=on:igrr=1/8:igrp=1400:igrpq=1.3:igs=1002:igwr=on:lcm=predicate:lma=on:nm=16:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:sp=reverse_arity_13");
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
      quick.push("ins+10_1_av=off:fde=none:gsp=on:irw=on:igbrr=0.7:igpr=on:igrr=16/1:igrp=400:igrpq=2.0:igs=1003:igwr=on:lcm=predicate:lma=on:nm=64:newcnf=on:nwc=3:sp=occurrence:uhcvi=on_62");
      quick.push("ins+11_64_av=off:cond=fast:fde=none:gs=on:gsem=on:igbrr=0.7:igrr=1/2:igrp=4000:igrpq=1.2:igwr=on:lcm=predicate:lma=on:nwc=1.1:sd=2:ss=axioms:st=3.0:sos=on:sp=occurrence_38");
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
      quick.push("ins+11_32_av=off:igbrr=0.4:igrr=1/64:igrpq=1.05:igwr=on:lcm=reverse:lma=on:nm=64:newcnf=on:nwc=1:sp=reverse_arity:updr=off_55");
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
      quick.push("ins+11_3_av=off:bd=off:igbrr=0.6:igrr=1/8:igrp=700:igrpq=2.0:igs=1:igwr=on:nwc=1:sd=3:ss=axioms:st=2.0:sos=on:updr=off_3");
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
    quick.push("ins+10_1_av=off:cond=on:fsr=off:gsp=on:igbrr=0.6:igpr=on:igrr=64/1:igrpq=1.5:igs=1010:igwr=on:lma=on:nwc=1:updr=off_9");
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
    fallback.push("ins+10_1_av=off:cond=on:fsr=off:gsp=on:igbrr=0.6:igpr=on:igrr=64/1:igrpq=1.5:igs=1010:igwr=on:lma=on:nwc=1:updr=off_300");
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
    fallback.push("ins+11_3_av=off:bd=off:igbrr=0.6:igrr=1/8:igrp=700:igrpq=2.0:igs=1:igwr=on:nwc=1:sd=3:ss=axioms:st=2.0:sos=on:updr=off_300");
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
    fallback.push("ins+10_1_av=off:igbrr=0.2:igpr=on:igrp=400:igrpq=2.0:igs=1:nwc=2.5:sos=theory_300");
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
    fallback.push("ins+1010_3_av=off:bd=off:igbrr=0.3:igpr=on:igrr=1/32:igrp=100:igrpq=1.3:igwr=on:lcm=predicate:lma=on:nm=2:nwc=1:sd=1:ss=axioms:sos=on:sp=occurrence:updr=off_300");
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
    fallback.push("ins+11_3_av=off:irw=on:igbrr=0.1:igpr=on:igrr=1/8:igrp=1400:igrpq=1.3:igs=1002:igwr=on:lcm=predicate:lma=on:nm=16:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:sp=reverse_arity_300");
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
    fallback.push("ins+11_32_av=off:igbrr=0.4:igrr=1/64:igrpq=1.05:igwr=on:lcm=reverse:lma=on:nm=64:newcnf=on:nwc=1:sp=reverse_arity:updr=off_300");
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
    quick.push("ins+11_2:3_av=off:cond=fast:fsr=off:gsp=on:ile=on:irw=on:igbrr=0.3:igpr=on:igrr=128/1:igrp=200:igrpq=1.3:igs=1003:igwr=on:lcm=reverse:lma=on:nm=2:newcnf=on:nwc=1:updr=off:uhcvi=on_195");
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
  fallback.push("ins+11_2:3_av=off:cond=fast:fsr=off:gsp=on:ile=on:irw=on:igbrr=0.3:igpr=on:igrr=128/1:igrp=200:igrpq=1.3:igs=1003:igwr=on:lcm=reverse:lma=on:nm=2:newcnf=on:nwc=1:updr=off:uhcvi=on_300");
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
  sched.push("ins+11_5_cond=fast:ep=RST:gs=on:gsem=on:igbrr=0.4:igpr=on:igrr=1/64:igrp=4000:igrpq=1.3:igwr=on:lcm=reverse:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:av=off:sp=occurrence:uhcvi=on_60"); // HH4 9 (81)
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
  sched.push("ins+11_5_cond=on:fsr=off:fde=none:gs=on:gsem=on:gsssp=full:igbrr=0.4:igrr=1/8:igrp=1400:igrpq=1.5:igwr=on:nwc=1:sd=1:ss=axioms:st=5.0:sos=on:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // HH4 86 (2)
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
  sched.push("ins+11_4_ep=RST:fsr=off:igrr=1/16:igrp=400:igrpq=2.0:igs=1:igwr=on:nm=0:nwc=1.3:sd=1:ss=axioms:st=5.0:av=off_60"); // HH4 103 (1)
  sched.push("ins+11_3_fsr=off:fde=none:gs=on:gsem=off:igbrr=0.5:igpr=on:igrr=1/4:igrp=2000:igrpq=1.2:igs=1003:igwr=on:nwc=10:sd=1:ss=axioms:av=off:sp=occurrence:urr=on:uhcvi=on_60"); // HH4 104 (1)
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
  sched.push("ins+11_4_cond=on:fde=none:gs=on:gsem=off:gsssp=full:igbrr=0.5:igpr=on:igrr=1/4:igrp=4000:igrpq=1.05:igs=1:igwr=on:nm=0:nwc=1:sd=1:ss=axioms:st=1.2:sos=all:av=off:sp=reverse_arity:updr=off:uhcvi=on_60"); // HH4 121 (1)
  sched.push("lrs+1002_3:1_bd=preordered:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=off:nm=0:nwc=3:stl=300:sd=4:ss=priority:sac=on:add=large:afp=10000:afq=1.0:amm=off:anc=none:uhcvi=on_60"); // HH4 122 (1)
  sched.push("dis+4_5:4_cond=on:fsr=off:fde=none:lwlo=on:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:av=off:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_60"); // HH4 123 (1)
  sched.push("ins+11_3_cond=fast:fsr=off:fde=none:igbrr=0.6:igrr=1/16:igrp=1400:igrpq=1.1:igs=1002:igwr=on:nm=0:nwc=1:sd=2:ss=priority:av=off:urr=ec_only:uhcvi=on_60"); // HH4 124 (1)
  sched.push("ott+11_2:1_gs=on:gsem=on:gsssp=full:nm=0:nwc=1:sd=2:ss=axioms:st=1.5:sac=on:add=large:afp=100000:afq=1.2:amm=sco:anc=all:sp=occurrence:updr=off:uhcvi=on_60"); // HH4 125 (1)
  sched.push("dis+1002_8_bd=off:fsr=off:fde=unused:gs=on:gsem=on:nwc=1:sd=4:ss=priority:sos=on:av=off:sp=occurrence_60"); // HH4 126 (1)
  sched.push("lrs+11_3_cond=fast:ep=RST:fde=unused:gs=on:gsem=on:nwc=1:stl=300:sd=3:ss=axioms:st=5.0:sos=all:av=off:updr=off:uhcvi=on_60"); // HH4 127 (1)
  sched.push("lrs+4_3:1_cond=fast:fsr=off:fde=unused:gs=on:gsem=off:lwlo=on:nm=0:nwc=1.7:stl=300:av=off:sp=reverse_arity:updr=off_60"); // HH4 128 (1)
  sched.push("ins+11_4_cond=on:fde=none:gsp=on:igbrr=0.8:igrp=1400:igs=1004:igwr=on:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:av=off:sp=reverse_arity_60"); // HH4 129 (1)
  sched.push("lrs-3_1_bd=off:cond=on:fde=none:gs=on:lcm=reverse:nm=0:nwc=1.1:stl=300:sd=2:ss=axioms:st=1.5:av=off:updr=off:uhcvi=on_60"); // HH4 130 (1)
  sched.push("lrs+11_5_bd=off:ccuc=first:fde=none:gs=on:lcm=reverse:nm=0:nwc=1:stl=300:sd=2:ss=priority:st=1.2:sos=all:aac=none:acc=model:afr=on:afp=1000:afq=1.1:anc=none:updr=off:uhcvi=on_60"); // HH4 131 (1)
  sched.push("lrs+11_5:4_cond=fast:fde=none:gs=on:gsaa=from_current:gsem=on:nwc=1:stl=300:sd=7:ss=axioms:st=3.0:sos=all:afp=10000:afq=1.1:amm=sco:anc=none:sp=reverse_arity:updr=off:uhcvi=on_60"); // HH4 132 (1)
  sched.push("dis+11_6_fsr=off:fde=none:gs=on:gsem=on:gsssp=full:lwlo=on:nm=0:nwc=1:sd=3:ss=axioms:sos=all:add=off:afr=on:afp=4000:afq=1.0:amm=sco:anc=all:sp=occurrence:urr=ec_only:uhcvi=on_60"); // HH4 133 (1)
  sched.push("lrs+1010_3:2_bd=off:bsr=unit_only:cond=fast:nwc=4:stl=300:sd=1:ss=axioms:st=3.0:sac=on:add=large:afp=10000:afq=1.2:amm=sco:sp=reverse_arity:updr=off:uhcvi=on_60"); // HH4 134 (1)
  sched.push("dis+1004_3:1_cond=fast:fde=unused:nm=0:nwc=1:sd=1:ss=axioms:st=1.2:sos=on:av=off:sp=reverse_arity:updr=off:uhcvi=on_60"); // HH4 135 (1)
  sched.push("dis+4_3_bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsssp=full:lwlo=on:nm=64:nwc=1:ss=axioms:st=2.0:sos=on:av=off:sp=occurrence:updr=off_60"); // HH4 136 (1)
  sched.push("lrs-10_24_bd=off:fsr=off:lcm=reverse:nm=0:nwc=1:stl=300:sd=1:ss=axioms:sos=on:av=off:sp=occurrence_60"); // HH4 137 (1)
  sched.push("ins+11_4_fde=none:igbrr=0.6:igpr=on:igrr=1/128:igrp=700:igrpq=1.05:igs=1002:igwr=on:lcm=predicate:nwc=1:sd=1:ss=axioms:sos=on:av=off:sp=occurrence:updr=off_60"); // HH4 138 (1)
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
  sched.push("ins+11_4_cond=fast:fde=none:igbrr=0.4:igrr=1/32:igrp=200:igrpq=1.2:igs=1003:igwr=on:nwc=10:sd=1:ss=axioms:st=5.0:av=off_60"); // ISA 19 (10)
  sched.push("lrs+1011_4:1_fsr=off:fde=unused:gs=on:gsem=on:gsssp=full:nm=64:nwc=4:stl=300:sd=1:ss=priority:st=3.0:aac=none:acc=on:afr=on:afp=40000:afq=1.2:amm=sco:anc=all:sp=reverse_arity:updr=off:uhcvi=on_60"); // ISA 20 (9)
  sched.push("dis+1002_50_fde=unused:nwc=1:sd=2:ss=axioms:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // ISA 21 (8)
  sched.push("ott+11_4_cond=fast:fde=none:gs=on:gsem=on:gsssp=full:nwc=1:sd=2:ss=axioms:sos=on:av=off:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // ISA 22 (8)
  sched.push("dis-3_3_ep=RST:fde=none:nm=64:nwc=1:sd=4:ss=axioms:sos=on:av=off:sp=occurrence:uhcvi=on_60"); // ISA 23 (7)
  sched.push("dis+1010_7_fsr=off:fde=unused:nm=0:nwc=1.3:nicw=on:sd=3:ss=priority:afr=on:afp=100000:afq=1.0:amm=sco:anc=none:updr=off:uhcvi=on_60"); // ISA 24 (7)
  sched.push("dis+1002_4_cond=fast:ep=RST:fsr=off:nwc=1:sd=3:ss=axioms:st=2.0:sos=on:afp=10000:afq=1.1:amm=sco:sp=occurrence:uhcvi=on_60"); // ISA 25 (6)
  sched.push("ott+1011_2_bd=off:ccuc=first:cond=on:fsr=off:fde=unused:gs=on:gsaa=from_current:gsem=on:nm=64:nwc=1.3:sd=3:ss=priority:st=1.2:sac=on:acc=on:add=off:afp=4000:afq=1.4:amm=sco:anc=none:urr=ec_only:updr=off:uhcvi=on_60"); // ISA 26 (6)
  sched.push("dis+1002_3_bd=off:gs=on:gsem=on:nwc=1.1:sd=7:ss=axioms:st=1.2:sos=on:av=off:sp=reverse_arity:updr=off_60"); // ISA 27 (5)
  sched.push("dis+11_2:3_cond=on:gs=on:gsem=off:gsssp=full:lcm=reverse:nwc=1:sd=1:ss=axioms:st=1.5:add=off:aer=off:afr=on:afp=1000:afq=2.0:anc=all_dependent:sp=reverse_arity:updr=off:uhcvi=on_60"); // ISA 28 (5)
  sched.push("ins+11_10_cond=on:gs=on:igbrr=0.3:igpr=on:igrr=1/32:igrp=100:igrpq=1.1:igs=1010:igwr=on:lcm=reverse:nwc=1.3:sd=1:ss=axioms:st=1.2:sos=on:av=off:sp=reverse_arity:urr=on:updr=off:uhcvi=on_60"); // ISA 29 (5)
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
  sched.push("ins+11_4_bd=off:fde=unused:gs=on:igbrr=0.6:igrr=1/16:igrp=4000:igrpq=1.3:igwr=on:lcm=predicate:nwc=1:sd=1:ss=axioms:st=1.5:sos=on:av=off:urr=on_60"); // ISA 54 (2)
  sched.push("ott+1011_10_fsr=off:fde=unused:nm=0:nwc=1:sd=3:ss=priority:st=1.2:av=off:uhcvi=on_60"); // ISA 55 (2)
  sched.push("ott+11_5:1_bd=off:cond=fast:nm=64:nwc=1.1:sd=3:ss=priority:st=2.0:av=off:sp=reverse_arity:urr=on:updr=off_60"); // ISA 56 (2)
  sched.push("lrs-3_3:1_cond=fast:ep=R:gsp=on:gs=on:gsem=on:gsssp=full:lcm=predicate:nwc=1:stl=300:sd=1:ss=axioms:st=3.0:sac=on:add=off:afr=on:afp=40000:afq=1.1:amm=sco:anc=none:uhcvi=on_60"); // ISA 57 (1)
  sched.push("dis+1011_2_cond=fast:ep=RST:fsr=off:fde=none:gs=on:gsem=off:gsssp=full:nwc=4:sd=2:ss=priority:sac=on:add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:sp=reverse_arity_60"); // ISA 58 (1)
  sched.push("dis+1002_4_cond=on:fde=none:gs=on:gsem=on:nwc=1:sd=4:ss=axioms:sos=on:av=off:sp=occurrence:uhcvi=on_60"); // ISA 59 (1)
  sched.push("dis-1_4_cond=fast:fsr=off:gs=on:gsem=off:gsssp=full:lcm=reverse:nwc=1:sd=1:ss=axioms:st=1.5:sos=on:av=off:updr=off:uhcvi=on_60"); // ISA 60 (1)
  sched.push("dis+10_4:1_fsr=off:gs=on:gsem=on:lcm=reverse:nm=64:nwc=1:sd=4:ss=priority:st=3.0:av=off:updr=off:uhcvi=on_60"); // ISA 61 (1)
  sched.push("dis+10_2_fsr=off:fde=none:lcm=reverse:lwlo=on:nm=64:nwc=1.2:sd=4:ss=priority:st=5.0:av=off:uhcvi=on_60"); // ISA 62 (1)
  sched.push("lrs+10_4_bd=off:cond=on:fde=unused:gs=on:gsem=off:lcm=predicate:nwc=1:stl=300:sd=2:ss=axioms:st=5.0:sos=on:av=off:urr=ec_only_60"); // ISA 63 (1)
  sched.push("ins+11_5_cond=on:ep=RST:fsr=off:fde=none:gsp=on:gs=on:gsem=on:igrr=1/8:igrpq=1.1:igs=1003:igwr=on:lcm=reverse:nwc=1:sd=1:ss=axioms:st=1.2:sos=on:av=off:sp=reverse_arity:urr=on:updr=off:uhcvi=on_60"); // ISA 64 (1)
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
  sched.push("ins+11_3_ep=RST:fde=unused:gsp=on:igbrr=0.4:igrr=1/8:igrpq=1.5:igs=1:igwr=on:lcm=predicate:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:av=off:updr=off:uhcvi=on_60"); // HLL 1 (1373)
  sched.push("lrs-4_5:4_bd=off:bs=unit_only:bsr=on:cond=on:fde=none:gs=on:gsaa=full_model:gsem=off:nm=0:nwc=1.1:nicw=on:stl=300:sd=1:ss=axioms:st=2.0:sos=on:sac=on:afr=on:afp=10000:afq=1.0:amm=off:anc=none:sp=reverse_arity:urr=on:updr=off_60"); // HLL 2 (382)
  sched.push("dis+1002_1_ep=RST:gs=on:gsaa=full_model:gsem=on:nm=64:nwc=1:sd=7:ss=axioms:st=1.2:sos=on:aer=off:afp=40000:afq=1.2:anc=none:updr=off:uhcvi=on_60"); // HLL 3 (170)
  sched.push("dis+1002_1_gs=on:gsem=off:nwc=1:sd=3:ss=axioms:sos=on:sac=on:afp=1000:afq=1.4:amm=sco:anc=none:sp=reverse_arity:urr=on_60"); // HLL 4 (148)
  sched.push("lrs+1011_4:1_bd=off:bsr=unit_only:ccuc=small_ones:fsr=off:fde=unused:gs=on:gsssp=full:nm=64:nwc=4:stl=300:sd=1:ss=priority:sac=on:acc=model:add=large:aer=off:afr=on:afp=100000:afq=1.2:anc=all:uhcvi=on_60"); // HLL 5 (68)
  sched.push("ins+11_5_br=off:ep=RST:fde=none:gsp=on:gs=on:gsem=on:igbrr=0.5:igpr=on:igrp=1400:igrpq=1.3:igs=1:igwr=on:nm=0:nwc=1:sd=1:ss=axioms:st=2.0:sos=all:av=off:urr=on:updr=off_60"); // HLL 6 (64)
  sched.push("lrs+10_1_bsr=unit_only:cond=fast:gs=on:gsem=off:gsssp=full:lcm=reverse:nwc=1:stl=300:sd=2:ss=axioms:st=5.0:sos=on:sac=on:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:sp=reverse_arity:urr=on:updr=off_60"); // HLL 7 (62)
  sched.push("dis+10_3:1_ep=RST:gsp=on:gs=on:gsem=on:lcm=reverse:nwc=1.1:sd=2:ss=priority:st=2.0:sos=on:sac=on:add=large:aer=off:afp=10000:afq=1.1:anc=none:sp=reverse_arity_60"); // HLL 8 (42)
  sched.push("lrs+1011_3:1_bd=off:bsr=on:cond=fast:gs=on:gsem=on:lwlo=on:nwc=10:stl=300:sd=1:ss=axioms:st=3.0:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // HLL 9 (35)
  sched.push("lrs+1011_5:1_fde=none:gs=on:gsem=on:nwc=4:stl=300:sd=1:ss=axioms:st=5.0:av=off:sp=occurrence:urr=on:uhcvi=on_60"); // HLL 10 (25)
  sched.push("ins+11_4_fsr=off:fde=unused:gsp=on:gs=on:igbrr=0.3:igrr=1/4:igrp=700:igrpq=1.3:igs=1:igwr=on:lcm=reverse:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:av=off:sp=reverse_arity:updr=off:uhcvi=on_60"); // HLL 11 (22)
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
  sched.push("ins+11_5_ep=RS:fsr=off:gs=on:igbrr=0.4:igpr=on:igrr=1/2:igrp=4000:igrpq=1.2:igs=1010:igwr=on:nwc=1:sd=1:ss=axioms:st=3.0:sos=all:av=off:sp=reverse_arity:urr=on:updr=off_60"); // HLL 35 (3)
  sched.push("dis+1010_2:3_bs=unit_only:bsr=unit_only:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:gsssp=full:nm=0:nwc=3:sd=4:ss=priority:st=1.5:sos=on:acc=on:add=off:aer=off:afr=on:afp=100000:afq=1.0:sp=reverse_arity:uhcvi=on_60"); // HLL 36 (3)
  sched.push("dis+1010_5:4_bd=off:fsr=off:fde=unused:gs=on:nm=64:nwc=1:sd=4:ss=axioms:st=1.2:sos=on:av=off:sp=reverse_arity:uhcvi=on_60"); // HLL 37 (3)
  sched.push("lrs+1011_8:1_bd=off:bsr=unit_only:fde=none:gs=on:lwlo=on:nm=0:nwc=1.5:stl=300:sd=1:ss=axioms:st=1.2:av=off:sp=occurrence:updr=off_60"); // HLL 38 (3)
  sched.push("dis+4_5:4_bd=off:fsr=off:fde=unused:gs=on:nwc=1:sd=5:ss=axioms:st=1.5:sos=all:av=off:sp=occurrence:uhcvi=on_60"); // HLL 39 (3)
  sched.push("dis+1011_3_cond=fast:ep=R:gs=on:gsem=off:lwlo=on:nm=0:nwc=1:sd=5:ss=axioms:st=1.5:sos=on:sac=on:add=large:afr=on:afp=1000:afq=1.1:anc=none:uhcvi=on_60"); // HLL 40 (2)
  sched.push("lrs+1004_3:1_bd=off:bsr=unit_only:cond=fast:fde=none:gs=on:gsem=off:gsssp=full:nwc=1:stl=300:sd=2:ss=axioms:sos=on:av=off:updr=off_60"); // HLL 41 (2)
  sched.push("lrs+10_1_bd=off:bsr=unit_only:cond=fast:fsr=off:fde=unused:gs=on:gsem=off:lcm=reverse:nwc=1:stl=300:sd=3:ss=axioms:st=1.5:av=off:sp=reverse_arity:urr=on_60"); // HLL 42 (2)
  sched.push("lrs+10_4_bd=off:bsr=unit_only:cond=on:gs=on:nwc=1:stl=300:sd=4:ss=axioms:st=5.0:sos=all:av=off:sp=reverse_arity:updr=off:uhcvi=on_60"); // HLL 43 (2)
  sched.push("ins+11_4_ep=RS:igbrr=0.6:igpr=on:igrr=1/128:igrp=2000:igrpq=2.0:igs=1002:igwr=on:nwc=1:sd=1:ss=axioms:sos=all:av=off:uhcvi=on_60"); // HLL 44 (2)
  sched.push("lrs+1010_2:3_bsr=unit_only:ccuc=small_ones:cond=on:fde=unused:gs=on:gsaa=full_model:nwc=1:stl=300:sd=2:ss=axioms:st=1.5:sos=on:sac=on:acc=model:add=off:aer=off:afr=on:afp=1000:afq=2.0:sp=occurrence:uhcvi=on_60"); // HLL 45 (2)
  sched.push("dis+10_1_bd=preordered:bs=unit_only:cond=on:fde=none:lcm=predicate:nwc=1:sd=2:ss=axioms:sos=all:sac=on:afr=on:amm=sco:anc=none:updr=off:uhcvi=on_60"); // HLL 46 (2)
  sched.push("lrs+11_5_bd=off:bsr=unit_only:cond=on:fsr=off:gs=on:gsaa=from_current:gsssp=full:nwc=1:stl=300:sd=1:ss=axioms:st=5.0:sos=all:add=off:afp=4000:afq=2.0:amm=off:anc=none:sp=occurrence:urr=on:updr=off:uhcvi=on_60"); // HLL 47 (2)
  sched.push("dis+11_2:1_br=off:ep=RST:fde=unused:gsp=on:gs=on:gsaa=from_current:gsem=off:nwc=1:sd=1:ss=priority:st=1.2:sos=all:add=large:aer=off:afp=100000:afq=1.1:anc=none:sp=occurrence:urr=on_60"); // HLL 48 (2)
  sched.push("dis+1011_2:3_cond=fast:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:gsssp=full:nm=0:nwc=1:sd=2:ss=axioms:sos=on:sac=on:add=large:afr=on:afp=1000:afq=2.0:anc=none:sp=reverse_arity:urr=ec_only:uhcvi=on_60"); // HLL 49 (2)
  sched.push("lrs+1003_4_bsr=unit_only:cond=fast:fsr=off:gsp=on:gs=on:gsaa=from_current:nm=0:nwc=1:stl=300:sos=on:sac=on:add=large:afp=10000:afq=1.1:anc=none:urr=ec_only:uhcvi=on_60"); // HLL 50 (1)
  sched.push("ins+11_4:1_cond=on:ep=RSTC:fde=none:gs=on:gsem=on:igbrr=0.2:igpr=on:igrr=32/1:igrp=2000:igrpq=1.3:igs=1002:igwr=on:nm=0:nwc=1:sd=2:ss=axioms:sos=all:av=off:sp=reverse_arity:uhcvi=on_60"); // HLL 51 (1)
  sched.push("dis+11_20_cond=fast:ep=R:fde=none:lwlo=on:nm=0:nwc=10:sd=4:ss=axioms:st=2.0:add=large:amm=off:sp=occurrence_60"); // HLL 52 (1)
  sched.push("lrs-2_3_bd=off:bs=unit_only:cond=on:fde=none:nwc=1:stl=300:sd=1:ss=axioms:st=1.2:sos=all:av=off:sp=occurrence:urr=ec_only:updr=off_60"); // HLL 53 (1)
  sched.push("lrs+11_3_bsr=unit_only:cond=on:ep=RST:fsr=off:fde=none:gs=on:gsem=off:gsssp=full:nwc=1:stl=300:sd=10:ss=axioms:st=1.5:sos=all:add=off:afp=40000:afq=1.0:anc=none:sp=occurrence:urr=on_60"); // HLL 54 (1)
  sched.push("lrs+1004_4_cond=on:fde=unused:gsp=on:gs=on:nwc=1:stl=300:sd=3:ss=axioms:st=5.0:sos=on:av=off:sp=occurrence:urr=on:updr=off_60"); // HLL 55 (1)
  sched.push("lrs+10_4_bsr=unit_only:cond=fast:fsr=off:fde=unused:gs=on:gsssp=full:nwc=1:stl=300:sd=2:ss=axioms:st=2.0:sos=on:afp=10000:afq=1.0:amm=sco:anc=all_dependent:sp=occurrence:uhcvi=on_60"); // HLL 56 (1)
  sched.push("dis+1011_3:1_cond=fast:fsr=off:fde=unused:lwlo=on:nwc=1:sd=2:ss=axioms:st=1.2:av=off:sp=reverse_arity:uhcvi=on_60"); // HLL 57 (1)
  sched.push("lrs-10_3:1_cond=fast:fde=unused:gs=on:gsaa=from_current:gsem=off:lcm=predicate:nwc=1:stl=300:sd=1:ss=axioms:sos=on:sac=on:add=off:afp=100000:afq=2.0:amm=sco:anc=none:sp=reverse_arity:uhcvi=on_60"); // HLL 58 (1)
  sched.push("lrs-10_3:1_bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=off:gsssp=full:lcm=reverse:nm=0:nwc=1:stl=300:sd=4:ss=axioms:st=1.5:sos=on:av=off:urr=ec_only:updr=off_60"); // HLL 59 (1)
  sched.push("ins+11_5_fde=unused:gsp=on:gs=on:igbrr=0.4:igrr=1/16:igrp=100:igrpq=1.5:igs=1002:igwr=on:lcm=predicate:nwc=1:sd=3:ss=axioms:st=2.0:sos=on:av=off:urr=ec_only_60"); // HLL 60 (1)
  sched.push("lrs+4_5_bd=off:fde=none:nwc=1.1:stl=300:sd=2:ss=axioms:st=5.0:sos=on:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // HLL 61 (1)
  sched.push("lrs-2_5:4_bd=off:bsr=unit_only:fsr=off:nm=0:nwc=1:stl=300:sd=2:ss=axioms:sos=on:av=off:sp=reverse_arity_60"); // HLL 62 (1)
  sched.push("lrs+11_5_bd=off:fde=none:gsp=on:gs=on:gsaa=full_model:gsssp=full:nwc=1:stl=300:sd=2:ss=priority:st=2.0:sos=all:sac=on:add=large:aer=off:afp=40000:afq=1.2:anc=none:uhcvi=on_60"); // HLL 63 (1)
  sched.push("lrs+11_24_bsr=unit_only:gsp=on:gs=on:gsem=off:gsssp=full:nm=0:nwc=1:stl=300:sd=2:ss=axioms:sos=all:sac=on:afp=1000:afq=1.0:amm=sco:anc=none:sp=reverse_arity:updr=off_60"); // HLL 64 (1)
  sched.push("ins+11_6_fsr=off:igbrr=0.4:igrr=1/64:igrp=100:igrpq=1.5:igs=1010:igwr=on:lcm=reverse:nwc=1:sd=2:ss=priority:av=off:sp=occurrence:updr=off_60"); // HLL 65 (1)
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
  sched.push("ins+11_3_cond=fast:igbrr=0.7:igpr=on:igrr=1/32:igrp=700:igrpq=1.5:igs=1003:igwr=on:nwc=1:sd=1:ss=axioms:st=3.0:sos=all:av=off:sp=occurrence:uhcvi=on_60"); // MZR 3 (81)
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
  sched.push("ins+11_4_bd=off:fsr=off:gsp=on:gs=on:gsem=off:igbrr=0.6:igpr=on:igrr=1/128:igrp=700:igrpq=1.2:igs=1004:igwr=on:lcm=predicate:nwc=1:sd=2:ss=axioms:st=5.0:sos=on:av=off:uhcvi=on_60"); // MZR 28 (3)
  sched.push("lrs+1011_1_cond=on:fsr=off:gs=on:nwc=1:stl=300:sd=4:ss=priority:st=1.2:sos=on:av=off:sp=reverse_arity:urr=on_60"); // MZR 29 (3)
  sched.push("lrs+11_3:1_bsr=unit_only:br=off:cond=on:ep=RST:fsr=off:gs=on:gsaa=from_current:gsem=off:nwc=3:stl=300:sd=2:ss=axioms:st=2.0:sac=on:add=large:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:sp=reverse_arity:urr=on_60"); // MZR 30 (3)
  sched.push("ins+11_3_cond=fast:fde=unused:igbrr=0.6:igrr=1/2:igrp=1400:igrpq=2.0:igs=1003:igwr=on:nwc=1:sos=on:av=off:updr=off_60"); // MZR 31 (3)
  sched.push("dis+11_5:4_ccuc=first:cond=on:er=known:fde=none:gs=on:nwc=1:sd=2:ss=priority:st=1.2:sos=all:aac=none:acc=model:add=large:afr=on:afp=10000:afq=1.2:anc=all_dependent:sp=reverse_arity:urr=on:uhcvi=on_60"); // MZR 32 (3)
  sched.push("lrs+1010_2_cond=on:fde=none:gs=on:gsem=off:nwc=1:stl=300:sd=3:ss=priority:st=1.2:sos=all:av=off:uhcvi=on_60"); // MZR 33 (3)
  sched.push("ins+11_4_fde=unused:gs=on:igbrr=0.7:igpr=on:igrr=1/4:igrp=100:igrpq=1.3:igs=1002:igwr=on:lcm=predicate:nwc=1:sd=3:ss=axioms:st=1.5:sos=all:av=off:sp=occurrence:urr=on:uhcvi=on_60"); // MZR 34 (3)
  sched.push("lrs+10_5:4_bd=off:ccuc=small_ones:cond=on:fde=none:gs=on:gsaa=from_current:gsem=off:nm=0:nwc=1:stl=300:sd=2:ss=priority:sos=on:acc=model:add=large:aer=off:afp=100000:afq=1.4:anc=none:urr=on_60"); // MZR 35 (2)
  sched.push("dis+11_1_ccuc=first:cond=on:fsr=off:fde=none:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1:nicw=on:sd=3:ss=priority:acc=model:add=large:afp=4000:afq=1.4:anc=all:sp=occurrence:updr=off:uhcvi=on_60"); // MZR 36 (2)
  sched.push("dis+1_1_fsr=off:gs=on:gsem=on:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:acc=on:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:sp=reverse_arity_60"); // MZR 37 (2)
  sched.push("dis+1004_2_bs=unit_only:bsr=unit_only:fde=unused:gs=on:nwc=1:sos=on:add=large:afr=on_60"); // MZR 38 (2)
  sched.push("dis+11_4_ep=RS:fde=none:gs=on:gsaa=full_model:gsem=off:nwc=1:sd=1:ss=priority:st=1.2:sos=all:sac=on:afp=10000:afq=1.1:amm=sco:anc=none:sp=reverse_arity:uhcvi=on_60"); // MZR 39 (2)
  sched.push("lrs+11_8_br=off:cond=on:fde=none:gs=on:gsem=on:gsssp=full:nwc=1:nicw=on:stl=300:sd=1:ss=axioms:st=5.0:sos=all:sac=on:add=off:afp=100000:afq=1.4:amm=off:anc=all:sp=reverse_arity:urr=on:uhcvi=on_60"); // MZR 40 (2)
  sched.push("ott+1_28_cond=fast:er=filter:fde=none:gsp=on:lcm=reverse:nwc=1.1:sos=on:av=off:sp=reverse_arity:updr=off:uhcvi=on_60"); // MZR 41 (2)
  sched.push("ins+10_5_cond=fast:fde=none:gsp=on:gs=on:gsem=on:igbrr=0.8:igrr=1/32:igrpq=1.5:igs=1003:igwr=on:nwc=1:sd=3:ss=priority:st=1.2:sos=all:av=off:sp=occurrence:urr=ec_only_60"); // MZR 42 (2)
  sched.push("dis+10_14_cond=fast:gs=on:gsaa=full_model:gsem=off:gsssp=full:nwc=1.5:sd=1:ss=axioms:st=1.5:afp=40000:afq=1.1:amm=sco:anc=none:sp=occurrence:updr=off_60"); // MZR 43 (2)
  sched.push("ins+11_5_cond=fast:fsr=off:fde=none:gsp=on:gs=on:gsem=off:igbrr=1.0:igrr=1/64:igrp=4000:igrpq=1.3:igs=1002:igwr=on:lcm=predicate:nm=0:nwc=1:sd=1:ss=axioms:st=3.0:sos=all:av=off:uhcvi=on_60"); // MZR 44 (2)
  sched.push("lrs+11_5_fde=none:gsp=on:gs=on:gsem=on:nwc=1:stl=300:sd=3:ss=axioms:st=3.0:sos=on:av=off:sp=occurrence:urr=on_60"); // MZR 45 (2)
  sched.push("lrs-10_4:1_cond=on:fsr=off:fde=unused:gsp=on:gs=on:gsem=on:nwc=1:stl=300:sd=3:ss=axioms:sos=on:av=off:urr=on_60"); // MZR 46 (2)
  sched.push("lrs+3_3:1_bd=preordered:bs=on:bsr=unit_only:fsr=off:fde=unused:gs=on:gsem=off:nwc=1:nicw=on:stl=300:sd=2:ss=axioms:st=3.0:sos=all:sac=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:sp=reverse_arity:urr=ec_only_60"); // MZR 47 (2)
  sched.push("dis+11_3_cond=fast:fsr=off:nwc=1:sd=1:ss=axioms:st=5.0:add=off:afr=on:afp=4000:afq=1.1:anc=none:sp=occurrence:updr=off_60"); // MZR 48 (1)
  sched.push("dis+11_4_bd=off:fsr=off:fde=unused:gs=on:gsaa=full_model:gsem=on:nwc=1:sd=1:ss=axioms:sac=on:add=large:afp=1000:afq=2.0:amm=sco:anc=none:sp=reverse_arity_60"); // MZR 49 (1)
  sched.push("dis+1010_2_bs=on:cond=fast:ep=RSTC:fde=unused:lwlo=on:nwc=1:sos=on:sac=on:add=off:afr=on:afp=10000:afq=1.4:sp=reverse_arity:uhcvi=on_60"); // MZR 50 (1)
  sched.push("dis+10_5_fsr=off:fde=unused:gs=on:gsem=on:gsssp=full:lcm=reverse:nwc=1:sd=2:ss=axioms:sos=on:add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:sp=occurrence:updr=off:uhcvi=on_60"); // MZR 51 (1)
  sched.push("lrs+1_4:1_br=off:cond=on:er=known:fsr=off:fde=unused:gs=on:nm=0:nwc=1:stl=600:sd=1:ss=priority:st=1.5:sos=on:sac=on:add=off:afp=4000:afq=1.1:amm=sco:anc=none:urr=on:updr=off:uhcvi=on_60"); // MZR 52 (1)
  sched.push("ins+11_10_cond=fast:fsr=off:gs=on:gsem=on:igbrr=0.5:igrr=1/2:igrpq=1.3:igs=1003:igwr=on:nwc=1:sd=2:ss=axioms:sos=on:av=off:sp=reverse_arity_60"); // MZR 53 (1)
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
  sched.push("ins+11_3_ep=RST:fde=unused:gsp=on:igbrr=0.4:igrr=1/8:igrpq=1.5:igs=1:igwr=on:lcm=predicate:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:av=off:updr=off:uhcvi=on_60"); // HLL 1 (1373)
  sched.push("lrs-4_5:4_bd=off:bs=unit_only:bsr=on:cond=on:fde=none:gs=on:gsaa=full_model:gsem=off:nm=0:nwc=1.1:nicw=on:stl=300:sd=1:ss=axioms:st=2.0:sos=on:sac=on:afr=on:afp=10000:afq=1.0:amm=off:anc=none:sp=reverse_arity:urr=on:updr=off_60"); // HLL 2 (382)
  sched.push("dis+1002_1_ep=RST:gs=on:gsaa=full_model:gsem=on:nm=64:nwc=1:sd=7:ss=axioms:st=1.2:sos=on:aer=off:afp=40000:afq=1.2:anc=none:updr=off:uhcvi=on_60"); // HLL 3 (170)
  sched.push("dis+1002_1_gs=on:gsem=off:nwc=1:sd=3:ss=axioms:sos=on:sac=on:afp=1000:afq=1.4:amm=sco:anc=none:sp=reverse_arity:urr=on_60"); // HLL 4 (148)
  sched.push("lrs+1011_4:1_bd=off:bsr=unit_only:ccuc=small_ones:fsr=off:fde=unused:gs=on:gsssp=full:nm=64:nwc=4:stl=300:sd=1:ss=priority:sac=on:acc=model:add=large:aer=off:afr=on:afp=100000:afq=1.2:anc=all:uhcvi=on_60"); // HLL 5 (68)
  sched.push("ins+11_5_br=off:ep=RST:fde=none:gsp=on:gs=on:gsem=on:igbrr=0.5:igpr=on:igrp=1400:igrpq=1.3:igs=1:igwr=on:nm=0:nwc=1:sd=1:ss=axioms:st=2.0:sos=all:av=off:urr=on:updr=off_60"); // HLL 6 (64)
  sched.push("lrs+10_1_bsr=unit_only:cond=fast:gs=on:gsem=off:gsssp=full:lcm=reverse:nwc=1:stl=300:sd=2:ss=axioms:st=5.0:sos=on:sac=on:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:sp=reverse_arity:urr=on:updr=off_60"); // HLL 7 (62)
  sched.push("dis+10_3:1_ep=RST:gsp=on:gs=on:gsem=on:lcm=reverse:nwc=1.1:sd=2:ss=priority:st=2.0:sos=on:sac=on:add=large:aer=off:afp=10000:afq=1.1:anc=none:sp=reverse_arity_60"); // HLL 8 (42)
  sched.push("lrs+1011_3:1_bd=off:bsr=on:cond=fast:gs=on:gsem=on:lwlo=on:nwc=10:stl=300:sd=1:ss=axioms:st=3.0:av=off:sp=occurrence:updr=off:uhcvi=on_60"); // HLL 9 (35)
  sched.push("lrs+1011_5:1_fde=none:gs=on:gsem=on:nwc=4:stl=300:sd=1:ss=axioms:st=5.0:av=off:sp=occurrence:urr=on:uhcvi=on_60"); // HLL 10 (25)
  sched.push("ins+11_4_fsr=off:fde=unused:gsp=on:gs=on:igbrr=0.3:igrr=1/4:igrp=700:igrpq=1.3:igs=1:igwr=on:lcm=reverse:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:av=off:sp=reverse_arity:updr=off:uhcvi=on_60"); // HLL 11 (22)
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
  sched.push("ins+11_3_cond=fast:igbrr=0.7:igpr=on:igrr=1/32:igrp=700:igrpq=1.5:igs=1003:igwr=on:nwc=1:sd=1:ss=axioms:st=3.0:sos=all:av=off:sp=occurrence:uhcvi=on_60"); // MZR 3 (81)
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
  sched.push("ins+11_5_cond=fast:ep=RST:gs=on:gsem=on:igbrr=0.4:igpr=on:igrr=1/64:igrp=4000:igrpq=1.3:igwr=on:lcm=reverse:nwc=1:sd=2:ss=axioms:st=1.2:sos=on:av=off:sp=occurrence:uhcvi=on_60"); // HH4 9 (81)
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
  sched.push("ins+11_5_ep=RS:fsr=off:gs=on:igbrr=0.4:igpr=on:igrr=1/2:igrp=4000:igrpq=1.2:igs=1010:igwr=on:nwc=1:sd=1:ss=axioms:st=3.0:sos=all:av=off:sp=reverse_arity:urr=on:updr=off_60"); // HLL 35 (3)
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
  sched.push("ins+11_4_cond=fast:fde=none:igbrr=0.4:igrr=1/32:igrp=200:igrpq=1.2:igs=1003:igwr=on:nwc=10:sd=1:ss=axioms:st=5.0:av=off_60"); // ISA 19 (10)
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
  sched.push("ins+11_4_ep=RS:igbrr=0.6:igpr=on:igrr=1/128:igrp=2000:igrpq=2.0:igs=1002:igwr=on:nwc=1:sd=1:ss=axioms:sos=all:av=off:uhcvi=on_60"); // HLL 44 (2)
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
  sched.push("ins+11_4_bd=off:fsr=off:gsp=on:gs=on:gsem=off:igbrr=0.6:igpr=on:igrr=1/128:igrp=700:igrpq=1.2:igs=1004:igwr=on:lcm=predicate:nwc=1:sd=2:ss=axioms:st=5.0:sos=on:av=off:uhcvi=on_60"); // MZR 28 (3)
  sched.push("dis+11_2:1_br=off:ep=RST:fde=unused:gsp=on:gs=on:gsaa=from_current:gsem=off:nwc=1:sd=1:ss=priority:st=1.2:sos=all:add=large:aer=off:afp=100000:afq=1.1:anc=none:sp=occurrence:urr=on_60"); // HLL 48 (2)
  sched.push("ins+11_10_cond=on:gs=on:igbrr=0.3:igpr=on:igrr=1/32:igrp=100:igrpq=1.1:igs=1010:igwr=on:lcm=reverse:nwc=1.3:sd=1:ss=axioms:st=1.2:sos=on:av=off:sp=reverse_arity:urr=on:updr=off:uhcvi=on_60"); // ISA 29 (5)
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
  quick.push("ott+1002_2_av=off:bd=preordered:csup=on:inj=on:chr=on:cases=on:cnfonf=lazy_not_gen_be_off:bet=on:suph=off:irw=on:lma=on:nm=64:nwc=10:sp=reverse_arity:updr=off_70");
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
  quick.push("ott+2_1:1_csup=on:fe=axiom:ntd=on:narr=off:prag=on:cs=on_600");
  quick.push("lrs+1010_3_av=off:fsr=off:csup=on:inj=on:chr=on:cases=on:cnfonf=eager:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_650");
  quick.push("dis-11_3_add=off:afp=0:fe=axiom:mXXn=2:csup=on:inj=on:chr=on:e2e=on:prag=on:cases=on:cnfonf=eager:afq=1.0:fde=all:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_600");
  quick.push("lrs+4_3_av=off:bd=preordered:fe=axiom:narr=off:csup=on:ntd=on:inj=on:chr=on:cases=on:cnfonf=lazy_simp:bs=unit_only:cond=fast:fde=unused:gsp=on:gs=on:gsem=on:lma=on:lwlo=on:nm=6:nwc=1:stl=60:sp=occurrence:uhcvi=on_600");
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

// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------
// ---------- ---------- ---------- ---------- ---------- ---------- ---------- ---------- ----------

void Schedules::getStructInductionSchedule(const Shell::Property& property, Schedule& quick, Schedule& fallback) {
  // Empirically sorted (order somewhat guessed)
  quick.push("lrs+10_1_ind=struct:sos=theory:sstl=1_89");
  quick.push("dis+1002_1_aac=none:anc=all:ind=struct:sos=theory:sac=on:sstl=1:to=lpo_30");
  quick.push("lrs+10_1_ind=struct:sos=theory:sstl=1:to=lpo_89");
  quick.push("lrs+10_1_drc=off:ind=struct:to=lpo_89");
  quick.push("lrs+10_1_drc=off:ind=struct:sos=theory:sstl=1:to=lpo_89");
  quick.push("lrs+10_1_ind=struct:to=lpo_89");
  quick.push("lrs+10_1_av=off:br=off:ind=struct:urr=on_89");
  quick.push("lrs+10_1_drc=off:ind=struct_89");
  quick.push("lrs+10_1_drc=off:ind=struct:sos=theory:sstl=1_89");
  quick.push("lrs+10_1_ind=struct_89");
  // The rest
  quick.push("lrs+10_1_drc=off:ind=struct:indoct=on:sos=theory:sstl=1:to=lpo_89");
  quick.push("lrs+10_1_drc=off:ind=struct:indoct=on:to=lpo_89");
  quick.push("lrs+10_1_ind=struct:indoct=on:sos=theory:sstl=1:to=lpo_89");
  quick.push("lrs+10_1_ind=struct:indoct=on:to=lpo_89");
  quick.push("lrs+10_1_drc=off:ind=struct:indoct=on:sos=theory:sstl=1_89");
  quick.push("lrs+10_1_drc=off:ind=struct:indoct=on_89");
  quick.push("lrs+10_1_ind=struct:indoct=on:sos=theory:sstl=1_89");
  quick.push("lrs+10_1_ind=struct:indoct=on_89");
  quick.push("lrs+10_1_drc=off:ind=struct:indgen=on:sos=theory:sstl=1:to=lpo_89");
  quick.push("lrs+10_1_drc=off:ind=struct:indgen=on:to=lpo_89");
  quick.push("lrs+10_1_ind=struct:indgen=on:sos=theory:sstl=1:to=lpo_89");
  quick.push("lrs+10_1_ind=struct:indgen=on:to=lpo_89");
  quick.push("lrs+10_1_drc=off:ind=struct:indgen=on:sos=theory:sstl=1_89");
  quick.push("lrs+10_1_drc=off:ind=struct:indgen=on_89");
  quick.push("lrs+10_1_ind=struct:indgen=on:sos=theory:sstl=1_89");
  quick.push("lrs+10_1_ind=struct:indgen=on_89");
  quick.push("lrs+10_1_drc=off:ind=struct:indgen=on:indoct=on:sos=theory:sstl=1:to=lpo_89");
  quick.push("lrs+10_1_drc=off:ind=struct:indgen=on:indoct=on:to=lpo_89");
  quick.push("lrs+10_1_ind=struct:indgen=on:indoct=on:sos=theory:sstl=1:to=lpo_89");
  quick.push("lrs+10_1_ind=struct:indgen=on:indoct=on:to=lpo_89");
  quick.push("lrs+10_1_drc=off:ind=struct:indgen=on:indoct=on:sos=theory:sstl=1_89");
  quick.push("lrs+10_1_drc=off:ind=struct:indgen=on:indoct=on_89");
  quick.push("lrs+10_1_ind=struct:indgen=on:indoct=on:sos=theory:sstl=1_89");
  quick.push("lrs+10_1_ind=struct:indgen=on:indoct=on_89");

  fallback.push("lrs+10_1__50");
}

void Schedules::getSnakeTptpUnsSchedule(const Shell::Property& property, Schedule& quick) {    
  if (property.hasNumerals() || property.hasInterpretedOperations()) { 
    // THA 
    quick.push("lrs+10_1:1024_fde=unused:to=lpo:sos=all:drc=off:fsr=off:i=10800:i=1_0");
    quick.push("lrs+10_1:8_gve=force:erd=off:fs=off:uwa=one_side_interpreted:nwc=2.0:i=120:ep=R:fsr=off:i=1_0");
    quick.push("lrs+10_1:1_to=lpo:tha=some:i=120:canc=force:i=1_0");
    quick.push("lrs+1002_1:1_drc=off:sp=reverse_frequency:sos=on:urr=on:br=off:s2a=on:i=120:canc=force:i=86_0");
    quick.push("lrs+10_1:1_gve=force:i=40000:ev=force:i=1_0");
    quick.push("dis+1002_1:1_gve=force:uwa=one_side_interpreted:uace=off:fd=off:nwc=1.8:s2a=on:i=105:s2at=5.0:i=21_0");
    quick.push("dis+1002_1:1_sos=on:spb=units:bd=off:sac=on:aac=none:i=240:i=1_0");
    quick.push("lrs+20_1:1_to=lpo:sos=on:spb=goal:fd=preordered:i=277:i=3_0");
    quick.push("lrs+1010_1:4_sos=on:spb=goal_then_units:alpa=true:nm=16:i=360:i=15_0");
    quick.push("dis+1011_1:1_nwc=5.0:i=40000:canc=force:bd=off:ev=cautious:i=16_0");
    quick.push("ott+1_4:1_si=on:rtra=on:rawr=on:plsq=on:plsqc=1:to=lpo:plsqr=32,1:drc=off:flr=on:s2pl=no:s2a=on:s2at=2.4:i=480:i=5_0");
    quick.push("lrs+10_1:1_gve=force:tha=off:i=120:i=4_0");
    quick.push("lrs+10_1:1_sas=z3:tha=off:sac=on:i=301:afp=1:i=165_0");
    quick.push("ott+1011_1:1_sp=reverse_frequency:sos=on:urr=on:flr=on:ss=axioms:ins=1:av=off:i=4440:i=6_0");
    quick.push("dis+1011_1:1024_awrs=decay:skr=on:st=2.0:s2a=on:sd=1:awrsf=32:ep=RSTC:ss=axioms:i=14640:i=3_0");
    quick.push("ott+21_1:1_to=lpo:sos=on:erd=off:urr=on:sac=on:st=3.0:s2a=on:sd=1:ss=included:sgt=64:i=240:i=21_0");
    quick.push("lrs+22_1:1_sos=on:gve=force:uwa=all:i=120:fsr=off:amm=sco:i=115_0");
    quick.push("lrs+1011_1:1_fs=off:urr=ec_only:br=off:tha=off:i=40000:fsr=off:i=369_0");
    quick.push("lrs+10_1:1_thi=strong:thigen=on:tha=off:i=40000:i=82_0");
    quick.push("lrs+10_1:32_tgt=ground:sas=z3:tha=off:newcnf=on:i=100000:i=227_0");
    quick.push("lrs+1002_1:1024_bsr=unit_only:to=lpo:sp=reverse_frequency:sos=on:urr=on:flr=on:newcnf=on:i=7800:av=off:i=8_0");
    quick.push("lrs+1010_1:2_sp=frequency:sos=on:st=3.0:ss=axioms:i=120:i=47_0");
    quick.push("lrs+1011_1:4_to=lpo:tgt=full:drc=off:spb=goal:nwc=2.0:i=40000:ins=1:av=off:bd=off:i=20_0");
    quick.push("dis+10_1:64_si=on:rtra=on:rawr=on:tha=off:nwc=1.4:i=120:i=21_0");
    quick.push("dis+21_1:1_anc=all:plsq=on:plsqr=25,6:sos=on:acc=model:lcm=reverse:uwa=one_side_constant:sac=on:i=120:canc=cautious:i=11_0");
    quick.push("ott+10_4:7_to=lpo:sp=reverse_frequency:sos=on:urr=on:bd=preordered:awrs=converge:nwc=10.0:flr=on:i=9240:i=12_0");
    quick.push("dis+1003_1:1_irw=on:sos=on:erd=off:spb=goal_then_units:ss=axioms:fsd=on:sgt=16:i=240:i=12_0");
    quick.push("lrs+1011_1:1_bsr=on:sos=on:st=2.0:i=62880:ss=included:i=1291_0");
    quick.push("lrs+2_1:1_si=on:rtra=on:rawr=on:to=lpo:sas=z3:fde=unused:sp=const_min:sos=on:spb=goal_then_units:urr=ec_only:lcm=reverse:avsqc=1:sac=on:avsq=on:avsqr=10,7:i=9260:aac=none:bd=off:amm=off:i=1658_0");
    quick.push("lrs+1011_1:1_slsqr=7,25:to=lpo:slsql=off:sp=frequency:drc=off:urr=ec_only:bce=on:slsq=on:slsqc=2:st=5.0:br=off:ss=included:av=off:fsr=off:i=1320:i=634_0");
    quick.push("lrs+2_1:1_sos=all:lma=on:spb=goal_then_units:urr=on:lcm=reverse:ss=included:i=240:i=20_0");
    quick.push("dis+10_1:1_bsr=unit_only:sfv=off:slsqr=3,2:drc=off:plsq=on:plsqc=1:plsqr=232,15:sp=weighted_frequency:sos=on:gve=cautious:abs=on:bce=on:lcm=reverse:fd=preordered:slsq=on:i=2520:aac=none:fsd=on:nm=16:bd=off:slsql=off:i=82_0");
    quick.push("lrs+10_1:1_sfv=off:thi=all:thigen=on:i=50000:i=85_0");
    quick.push("dis+3_1:4_sos=all:sd=7:ss=axioms:av=off:sfv=off:sgt=16:i=5040:i=43_0");
    quick.push("ott+1011_1:2_bsr=unit_only:urr=on:s2agt=32:nwc=5.0:s2a=on:bs=unit_only:br=off:i=20160:i=25_0");
    quick.push("lrs+11_1:1024_to=lpo:sp=weighted_frequency:thsqr=1376520,872807:urr=on:rnwc=on:br=off:nwc=1.2:flr=on:bs=unit_only:i=488:thsqd=64:awrs=converge:thsqc=32:thsq=on:i=28_0");
    quick.push("lrs+2_1:128_si=on:rtra=on:rawr=on:drc=off:spb=units:thsqr=4,7:nwc=1.94:lwlo=on:i=287832:thsqd=32:awrs=decay:awrsf=20:fsd=on:nm=2:thsqc=32:thsq=on:i=86_0");
    quick.push("lrs+1010_5:1_sas=z3:norm_ineq=on:sos=all:tha=off:i=240:aer=off:ss=axioms:i=221_0");
    quick.push("lrs+10_1:1_thi=overlap:plsq=on:plsqc=1:plsqr=32,1:tha=off:i=40000:i=653_0");
    quick.push("lrs+1011_1:16_tgt=ground:drc=off:s2a=on:i=40000:bd=preordered:i=48_0");
    quick.push("lrs+1002_1:1_fs=off:urr=ec_only:br=off:tha=off:i=40000:av=off:fsr=off:i=398_0");
    quick.push("lrs+10_1:1_to=lpo:sp=frequency:acc=model:urr=on:nwc=5.0:sac=on:newcnf=on:s2a=on:br=off:ins=1:i=480:i=100_0");
    quick.push("lrs+1011_1:1_slsqr=1,4:sas=z3:norm_ineq=on:fde=none:sp=reverse_frequency:br=off:nwc=10.0:slsqc=2:slsq=on:i=240:slsql=off:i=156_0");
    quick.push("lrs+21_8:1_bsr=unit_only:sas=z3:spb=units:abs=on:lcm=predicate:fd=preordered:i=40000:nm=32:bd=off:ev=cautious:i=113_0");
    quick.push("lrs+1010_1:1_tgt=ground:sas=z3:tha=off:nwc=3.0:i=40000:i=664_0");
    quick.push("lrs+10_1:1_urr=on:br=off:s2agt=8:st=2.0:s2a=on:i=11760:ss=axioms:i=245_0");
    quick.push("lrs+10_1:6_sas=z3:plsq=on:fde=none:to=lpo:sp=reverse_frequency:drc=off:fd=preordered:s2a=on:bs=on:ss=included:ins=1:i=3240:i=160_0");
    quick.push("dis+21_3:1_to=lpo:sas=z3:fde=none:spb=goal_then_units:abs=on:nwc=3.0:newcnf=on:s2a=on:i=5400:s2at=2.0:nm=2:fsr=off:i=322_0");
    quick.push("lrs+31_1:1_sas=z3:urr=on:uace=off:tha=some:avsqc=2:sac=on:sffsmt=on:avsq=on:s2a=on:i=230:afp=10:ep=RS:i=112_0");
    quick.push("dis+1010_1:1_tgt=full:tha=off:nwc=1.5:i=40000:nm=0:av=off:i=397_0");
    quick.push("dis+1002_1:1_to=lpo:tgt=ground:sas=z3:abs=on:tha=some:sac=on:nicw=on:i=40000:aac=none:i=617_0");
    quick.push("dis+33_1:1_pum=on:plsq=on:sas=z3:abs=on:tha=off:nwc=10.0:updr=off:s2a=on:i=40000:canc=cautious:bd=off:ev=cautious:i=441_0");
    quick.push("lrs+1011_1:1_plsq=on:plsqr=1,32:sp=occurrence:sos=on:acc=model:plsql=on:gs=on:skr=on:flr=on:updr=off:sac=on:newcnf=on:avsq=on:s2a=on:i=3480:s2at=3.0:fsd=on:bd=off:i=147_0");
    quick.push("dis+1011_1:1_slsqr=1,8:to=lpo:plsq=on:sp=frequency:slsqc=0:slsq=on:s2a=on:i=24480:s2at=3.0:nm=6:av=off:fsr=off:i=5601_0");
    quick.push("lrs+1010_1:1_to=lpo:tgt=full:sas=z3:spb=goal:uwa=all:br=off:tha=some:i=100000:bd=off:i=172_0");
    quick.push("lrs+1011_4:1_plsq=on:plsqc=1:sas=z3:plsqr=8,27:sp=unary_frequency:spb=intro:abs=on:urr=on:plsql=on:br=off:nwc=3.0:skr=on:sffsmt=on:s2a=on:i=40000:s2at=2.0:kws=inv_arity_squared:afp=10:canc=force:asg=cautious:bd=off:afq=1.45:ev=force:i=589_0");
    quick.push("lrs+1002_1:1_urr=ec_only:i=31080:sd=1:nm=0:ss=axioms:i=4805_0");
    quick.push("lrs+10_1:128_to=lpo:drc=off:sas=z3:norm_ineq=on:fde=none:sp=reverse_arity:sos=all:gve=force:spb=intro:uwa=one_side_constant:i=720:asg=cautious:ss=axioms:i=224_0");
    quick.push("lrs+11_1:1_sas=z3:norm_ineq=on:erd=off:fs=off:tha=some:nwc=10.0:s2a=on:i=480:s2at=3.0:fsr=off:i=244_0");
    quick.push("lrs+1011_1:6_bsr=unit_only:sfv=off:to=lpo:sas=z3:fde=unused:sp=weighted_frequency:spb=units:bce=on:tha=off:nwc=3.0:s2agt=40:newcnf=on:cond=fast:s2a=on:i=3360:aac=none:canc=cautious:afr=on:i=271_0");
    quick.push("lrs+10_1:3_anc=all_dependent:slsqr=13,121:to=lpo:bsd=on:sas=z3:sp=reverse_arity:gve=force:lma=on:urr=ec_only:uace=off:br=off:tha=some:fd=preordered:gs=on:s2agt=4:slsqc=1:updr=off:slsq=on:cond=fast:avsq=on:avsqr=21,226:i=900:s2at=1.9:add=large:awrs=decay:awrsf=47:canc=cautious:ins=1:fsr=off:fsd=on:uhcvi=on:afr=on:i=302_0");
    quick.push("dis+31_1:1_sas=z3:norm_ineq=on:urr=on:lcm=reverse:tha=off:nwc=10.0:i=600:i=356_0");
    quick.push("lrs+1002_1:10_sas=z3:norm_ineq=on:fde=none:sos=on:erd=off:abs=on:uwa=one_side_interpreted:uace=off:tha=some:flr=on:i=960:asg=force:nm=0:fsr=off:bd=off:i=423_0");
    quick.push("ott+10_1:1_sp=reverse_frequency:drc=off:bd=preordered:fd=preordered:nwc=5.0:i=18840:i=438_0");
    quick.push("lrs+1004_4:1_sims=off:sos=all:bd=off:skr=on:st=2.0:sd=1:ss=axioms:i=44880:i=599_0");
    quick.push("dis+1011_1:1_sfv=off:slsqr=46,31:tgt=ground:thi=overlap:sas=z3:sp=const_frequency:abs=on:thsqr=7,4:tha=some:slsqc=2:flr=on:slsq=on:thitd=on:i=40000:s2at=3.0:thsqd=32:nm=0:bd=off:thsqc=32:thsq=on:i=21133_0");
    quick.push("lrs+10_1:1_thi=all:sas=z3:abs=on:thigen=on:tha=off:nwc=10.0:s2a=on:i=40000:ev=cautious:i=1840_0");
    quick.push("lrs+1010_1:1_to=lpo:sims=off:sas=z3:abs=on:tha=off:fd=off:i=40000:aac=none:nm=0:bd=off:i=11081_0");
    quick.push("dis+1010_137062:920759_si=on:rtra=on:rawr=on:anc=none:sfv=off:tgt=ground:fde=unused:bsd=on:sas=z3:gve=cautious:erd=off:spb=goal:abs=on:bce=on:atotf=0.5:uwa=all:gs=on:nwc=3.3:thsql=off:skr=on:avsqc=2:sac=on:newcnf=on:avsq=on:avsqr=383,440:i=8400:aac=none:asg=cautious:amm=sco:thsqc=128:thsq=on:i=949_0");
    quick.push("dis+1002_1:1_sas=z3:plsq=on:plsqc=2:sp=const_frequency:foolp=on:abs=on:urr=on:bce=on:rnwc=on:uwa=one_side_interpreted:tha=off:nwc=5.0:thsql=off:cond=on:bs=on:i=6240:thsqd=32:ep=RSTC:amm=off:thsqc=64:ss=axioms:thsq=on:sgt=8:i=5217_0");
    quick.push("lrs+10_1:1_sos=all:st=4.0:i=60000:sd=10:av=off:ss=axioms:i=10410_0");
    quick.push("dis+10_1:64_si=on:rtra=on:rawr=on:slsqr=1,1:s2agt=16:slsqc=1:slsq=on:s2a=on:i=13080:i=1398_0");
    quick.push("lrs+1011_1:1_drc=off:norm_ineq=on:sp=frequency:gve=force:erd=off:urr=on:bce=on:tha=some:sac=on:i=3960:ins=2:i=3055_0");
    quick.push("lrs+10_1:1_tgt=ground:sas=z3:tha=off:newcnf=on:i=40000:i=1581_0");
    quick.push("lrs+10_1:1024_urr=on:br=off:i=55800:ep=RSTC:i=42453_0");
    quick.push("lrs+1002_1:18_tgt=ground:thi=strong:fde=none:sims=off:bsd=on:sas=z3:sp=reverse_arity:gve=cautious:spb=goal:abs=on:bce=on:thigen=on:rnwc=on:uwa=all:tha=off:fd=preordered:gs=on:nwc=1.2:kmz=on:skr=on:flr=on:gsem=off:cond=fast:s2a=on:i=40000:add=off:gsaa=from_current:kws=precedence:canc=force:nm=0:amm=off:afr=on:i=2357_0");
    quick.push("ott+10_6715:511922_si=on:rtra=on:rawr=on:drc=off:sp=frequency:spb=goal_then_units:uwa=interpreted_only:fd=preordered:nwc=5.0:bs=on:i=51000:awrs=decay:awrsf=1:bd=preordered:i=3014_0");
    quick.push("lrs+10_1:1_sos=all:i=32400:ep=RS:fsr=off:i=8782_0");
    quick.push("lrs+11_9:8_sas=z3:bsd=on:etr=on:lma=on:tha=some:nwc=3.0:s2agt=10:newcnf=on:s2a=on:i=11160:fsd=on:nm=0:fsr=off:amm=off:i=3775_0");
    quick.push("lrs+35_1:1_norm_ineq=on:abs=on:tha=off:s2a=on:i=17880:s2at=3.0:aac=none:amm=off:i=17678_0");
    quick.push("lrs+10_1:1_tgt=full:sas=z3:spb=goal:uwa=ground:tha=off:newcnf=on:i=100000:ev=force:i=6617_0");
    quick.push("lrs+1002_5:1_sfv=off:thi=neg_eq:sp=const_frequency:fd=preordered:cond=on:i=232604:thsqd=64:awrs=decay:awrsf=16:av=off:thsqc=16:thsq=on:i=9822_0");
    quick.push("lrs+10_1:1_tgt=ground:sas=z3:abs=on:uwa=all:tha=off:nicw=on:i=40000:afp=1000:i=13231_0");
    quick.push("ott+0_1:128_anc=none:to=lpo:sas=z3:irw=on:norm_ineq=on:thi=strong:fde=unused:bsd=on:etr=on:sos=all:gve=force:spb=units:uwa=one_side_interpreted:tha=off:flr=on:cond=fast:i=27960:awrs=converge:awrsf=110:fsd=on:amm=sco:afr=on:i=13992_0");
    quick.push("ott+10_1:64_to=lpo:uwa=one_side_interpreted:nwc=5.0:i=101760:bd=preordered:i=50584_0");
    quick.push("lrs+10_3:1_to=lpo:sas=z3:sos=all:abs=on:newcnf=on:i=53760:sd=1:ep=RST:nm=2:ss=included:i=50697_0");
    quick.push("lrs+20_1:1_i=100000:kws=precedence:fsr=off:i=80856_0");
    quick.push("lrs+10_2:3_si=on:rtra=on:rawr=on:tha=off:lwlo=on:bs=on:i=203445:i=193897_0");
    quick.push("lrs+30_1:64_to=lpo:sp=frequency:flr=on:i=129600:i=120799_0");
  } else if (property.category() == Property::Category::UEQ) {
    // UEQ
    quick.push("lrs+10_1:1_drc=off:lwlo=on:av=off:i=2280:i=1468_0");
    quick.push("lrs+10_1:1_sos=all:urr=on:br=off:i=1560:ep=RSTC:i=1_0");
    quick.push("lrs+10_1:16_sos=on:urr=on:awrs=converge:nwc=3.0:flr=on:awrsf=40:br=off:ep=RSTC:gsp=on:i=360:i=110_0");
    quick.push("lrs+10_1:1_to=lpo:drc=off:sp=reverse_frequency:spb=goal:i=120:i=34_0");
    quick.push("lrs+1010_1:1_to=lpo:sp=frequency:sos=on:i=960:sd=1:ss=included:i=25_0");
    quick.push("ott+10_1:12_to=lpo:drc=off:plsq=on:fde=unused:spb=goal:uwa=interpreted_only:thsql=off:i=568:thsqd=32:bd=preordered:thsqc=32:thsq=on:i=274_0");
    quick.push("lrs+10_1:1_sfv=off:to=lpo:sos=all:lma=on:spb=goal_then_units:i=120:av=off:bd=off:i=4_0");
    quick.push("dis+1011_1:64_drc=off:urr=ec_only:nwc=2.0:flr=on:sac=on:i=3600:i=972_0");
    quick.push("lrs+10_1:6_tgt=full:drc=off:i=40000:bd=off:i=32849_0");
    quick.push("ott+10_4:7_to=lpo:sp=reverse_frequency:sos=on:urr=on:bd=preordered:awrs=converge:nwc=10.0:flr=on:i=9240:i=7_0");
    quick.push("dis+10_1:7_to=lpo:drc=off:plsq=on:sp=reverse_frequency:fd=preordered:i=360:i=193_0");
    quick.push("lrs+10_7:2_slsqr=5,8:to=lpo:drc=off:fde=unused:sp=const_min:spb=units:fd=preordered:slsqc=2:slsq=on:i=1560:awrs=decay:awrsf=8:fsr=off:bd=preordered:i=62_0");
    quick.push("lrs+1002_1:1_bsr=on:slsqr=292,253:fde=none:to=lpo:sims=off:etr=on:sp=frequency:drc=off:urr=ec_only:slsq=on:nwc=10.0:slsqc=0:newcnf=on:st=1.5:s2a=on:bs=on:ss=axioms:fsd=on:av=off:fsr=off:gs=on:fsdmm=1:i=3000:i=118_0");
    quick.push("dis+1002_1:12_tgt=full:drc=off:fd=preordered:i=100000:i=98323_0");
    quick.push("lrs+10_5:1_bsr=unit_only:to=lpo:sp=reverse_arity:sos=all:urr=on:bce=on:bd=off:st=2.0:s2a=on:ss=axioms:i=960:i=20_0");
    quick.push("ott+10_1:1_to=lpo:drc=off:fde=unused:sp=frequency:spb=goal_then_units:uwa=all:nwc=3.0:s2pl=no:i=4500:s2at=3.0:ins=2:gsp=on:i=22_0");
    quick.push("dis+10_1:14_tgt=ground:sp=unary_first:i=40000:awrs=converge:i=83_0");
    quick.push("dis+21_1:1_fde=unused:sp=frequency:erd=off:lcm=predicate:fd=off:nwc=3.0:s2a=on:i=120:s2at=2.0:er=filter:i=32_0");
    quick.push("ott+10_1:8_si=on:rtra=on:rawr=on:sp=occurrence:drc=off:awrs=decay:awrsf=4:ss=axioms:ins=3:i=40320:i=110_0");
    quick.push("lrs+10_1:1_to=lpo:sos=on:spb=goal_then_units:sd=1:ss=included:i=3360:i=37_0");
    quick.push("lrs+10_1:32_urr=on:br=off:st=2.0:i=240:sd=2:nm=16:ss=axioms:i=37_0");
    quick.push("lrs+3_1:1_tgt=ground:sp=weighted_frequency:spb=intro:atotf=0.2:i=40000:kws=precedence:fsr=off:i=10778_0");
    quick.push("lrs+10_8:1_sp=reverse_frequency:drc=off:bd=preordered:fd=preordered:i=6480:i=4209_0");
    quick.push("lrs+10_1:64_to=lpo:drc=off:plsq=on:plsqc=1:sp=frequency:spb=goal_then_units:urr=on:uwa=all:fd=preordered:slsq=on:i=163:bd=preordered:i=58_0");
    quick.push("lrs+10_1:1_si=on:rtra=on:rawr=on:to=lpo:drc=off:plsq=on:sp=occurrence:fd=preordered:i=120:i=69_0");
    quick.push("lrs+1011_8:1_si=on:rtra=on:rawr=on:plsq=on:plsqr=278,15:spb=goal_then_units:urr=ec_only:br=off:fd=off:slsqc=1:slsq=on:i=3240:s2at=1.5:bd=off:i=75_0");
    quick.push("lrs+10_1:1_bsr=unit_only:slsqr=211,119:to=lpo:drc=off:avsql=on:sp=reverse_frequency:spb=goal_then_units:rnwc=on:inw=on:nwc=10.0:slsqc=0:slsq=on:st=2.0:avsq=on:i=12360:fsr=off:ss=included:sgt=16:slsql=off:i=4820_0");
    quick.push("lrs+35_1:4_bsr=unit_only:slsqr=1,2:sp=frequency:lcm=reverse:slsqc=1:flr=on:slsq=on:i=409:av=off:slsql=off:i=353_0");
    quick.push("dis+10_5:1_to=lpo:drc=off:sp=reverse_arity:sos=all:spb=goal:i=240:i=182_0");
    quick.push("lrs+10_1:8_fde=unused:sp=reverse_frequency:drc=off:fd=preordered:st=2.0:ss=axioms:i=12600:i=2137_0");
    quick.push("lrs+10_1:2_to=lpo:drc=off:fde=unused:sp=const_min:fd=preordered:i=360:bd=preordered:i=131_0");
    quick.push("ott+10_1:1_slsqr=10,31:to=lpo:tgt=ground:drc=off:fde=unused:sp=const_min:urr=ec_only:slsq=on:i=40000:bd=preordered:i=26948_0");
    quick.push("dis+2_1:1024_si=on:rtra=on:rawr=on:anc=all_dependent:slsqr=1,1:sp=reverse_arity:abs=on:drc=off:bce=on:slsq=on:slsqc=0:alpa=false:newcnf=on:avsq=on:i=28680:i=168_0");
    quick.push("lrs+10_1:32_drc=off:i=7080:i=6388_0");
    quick.push("dis+10_1:128_tgt=ground:drc=off:sp=const_frequency:i=40000:ins=1:i=33007_0");
    quick.push("ott+10_1:1_si=on:rtra=on:rawr=on:slsqr=5,3:drc=off:sp=weighted_frequency:urr=on:slsqc=1:flr=on:slsq=on:s2a=on:i=300:slsql=off:i=214_0");
    quick.push("dis+10_1:1_slsqr=29,16:to=lpo:drc=off:sp=reverse_frequency:slsqc=1:slsq=on:i=1080:av=off:i=221_0");
    quick.push("lrs+10_1:1_si=on:rtra=on:rawr=on:plsq=on:plsqr=32,1:urr=on:br=off:newcnf=on:i=60720:ep=RSTC:i=1901_0");
    quick.push("dis+1003_1:128_to=lpo:tgt=full:sp=unary_frequency:nwc=5.0:s2a=on:i=40000:av=off:i=509_0");
    quick.push("lrs+1010_1:3_si=on:rtra=on:rawr=on:anc=all_dependent:slsqr=10,119:sas=z3:plsq=on:plsqc=2:avsqr=51857,726697:sp=weighted_frequency:bce=on:bd=off:plsql=on:slsq=on:slsqc=0:amm=off:avsq=on:aac=none:ss=axioms:nm=16:afr=on:i=6720:i=300_0");
    quick.push("lrs+10_1:512_bsr=unit_only:slsqr=1,16:tgt=full:drc=off:irw=on:plsq=on:plsqc=2:plsqr=9798671,477100:sp=weighted_frequency:foolp=on:gve=cautious:erd=off:spb=intro:urr=on:lcm=reverse:plsql=on:uwa=ground:br=off:nwc=5.0:slsqc=1:kmz=on:updr=off:newcnf=on:slsq=on:i=17850:kws=arity_squared:awrs=converge:awrsf=8:av=off:bd=preordered:fsd=on:i=613_0");
    quick.push("lrs+10_1:1_si=on:rtra=on:rawr=on:bsr=on:to=lpo:plsq=on:plsqc=2:sas=z3:plsqr=217,15:sp=occurrence:abs=on:urr=on:uwa=all:br=off:nwc=3.0:s2agt=32:skr=on:newcnf=on:s2a=on:i=100000:afp=1000:thsqc=64:thsq=on:er=known:i=3405_0");
    quick.push("ott+10_1:4_si=on:rtra=on:rawr=on:tgt=full:sp=occurrence:i=40000:bd=preordered:i=686_0");
    quick.push("lrs+10_1:6_sas=z3:plsq=on:fde=none:to=lpo:sp=reverse_frequency:drc=off:fd=preordered:s2a=on:bs=on:ss=included:ins=1:i=3240:i=349_0");
    quick.push("dis+11_1:64_fd=off:nwc=5.0:i=40000:nm=0:i=367_0");
    quick.push("dis+10_1:16_tgt=ground:i=40000:ins=2:i=1485_0");
    quick.push("dis+1011_1:2_to=lpo:tgt=ground:sp=const_max:spb=goal:flr=on:s2a=on:i=100000:s2at=1.5:av=off:i=429_0");
    quick.push("lrs+10_1:32_tgt=full:drc=off:i=40000:kws=inv_frequency:awrs=converge:i=4436_0");
    quick.push("ott+10_1:1_irw=on:bsd=on:sos=on:spb=units:abs=on:urr=on:bce=on:bd=off:flr=on:s2a=on:bs=unit_only:s2at=1.35:br=off:fsd=on:i=18720:i=1240_0");
    quick.push("ott+10_1:1_slsqr=1,1:urr=on:slsqc=2:slsq=on:st=2.0:i=61560:ss=included:i=643_0");
    quick.push("lrs+1010_1:173_anc=none:sfv=off:drc=off:bsd=on:sp=reverse_arity:erd=off:acc=on:urr=ec_only:bce=on:nwc=3.0:alpa=true:skr=on:flr=on:updr=off:nicw=on:cond=on:st=2.0:avsq=on:avsqr=497233,912204:bs=on:i=21480:sd=2:awrs=decay:awrsf=4:nm=16:aer=off:gsp=on:ss=axioms:i=1652_0");
    quick.push("ott+1_1:1_si=on:rtra=on:rawr=on:slsqr=1,1:plsq=on:slsqc=2:slsq=on:st=1.5:s2a=on:i=1080:s2at=2.0:nm=21:ss=included:i=841_0");
    quick.push("ott+32_8:1_to=lpo:drc=off:foolp=on:spb=goal_then_units:nwc=10.0:s2agt=8:thsql=off:flr=on:dr=on:cond=fast:s2a=on:i=8280:thsqd=16:nm=16:av=off:thsqc=64:thsq=on:i=2310_0");
    quick.push("lrs+10_1:128_slsqr=40,29:slsql=off:drc=off:bd=off:awrs=converge:slsq=on:slsqc=1:awrsf=8:i=1680:i=1218_0");
    quick.push("lrs+10_1:12_sp=frequency:spb=goal_then_units:drc=off:ins=1:i=29160:i=8729_0");
    quick.push("lrs+1011_1:4_to=lpo:tgt=full:drc=off:spb=goal:nwc=2.0:i=40000:ins=1:av=off:bd=off:i=6239_0");
    quick.push("dis+2_1:1_to=lpo:plsq=on:plsqc=1:plsqr=32,1:sp=reverse_frequency:urr=ec_only:uwa=all:flr=on:i=40800:av=off:i=4713_0");
    quick.push("dis+10_1:1_bsr=on:to=lpo:drc=off:plsq=on:plsqr=13,2:sp=const_max:i=40440:bd=off:i=1709_0");
    quick.push("dis+1011_1:16_slsqr=1,16:drc=off:acc=on:urr=on:fd=preordered:nwc=2.0:slsqc=2:slsq=on:i=12360:thsqd=16:fsd=on:thsqc=16:thsq=on:slsql=off:i=5173_0");
    quick.push("dis+1003_1:1_fde=unused:bsd=on:nwc=5.0:s2agt=32:s2a=on:i=9120:fsd=on:i=1844_0");
    quick.push("dis+10_1:512_tgt=ground:drc=off:sp=unary_first:spb=intro:fd=preordered:s2a=on:i=40000:kws=precedence:ins=2:i=7848_0");
    quick.push("dis+10_1:64_si=on:rtra=on:rawr=on:slsqr=1,1:s2agt=16:slsqc=1:slsq=on:s2a=on:i=13080:i=4714_0");
    quick.push("ins+10_1:1_drc=off:st=3.0:igwr=on:igrr=1/8:ss=axioms:igs=1002:i=8160:i=2573_0");
    quick.push("lrs+10_37:16_plsq=on:plsqc=1:spb=goal_then_units:drc=off:plsql=on:awrs=decay:fd=preordered:lwlo=on:awrsf=16:i=53760:i=17656_0");
    quick.push("lrs+10_1:2_tgt=full:drc=off:sp=frequency:i=40000:i=12575_0");
    quick.push("ott+10_75:754_anc=all:slsqr=1,1:fde=unused:to=lpo:add=large:spb=goal_then_units:abs=on:drc=off:atotf=0.3115:fd=preordered:slsq=on:nwc=4.0:slsqc=1:nicw=on:gsem=off:gsaa=from_current:gs=on:i=100560:i=49679_0");
    quick.push("dis+1011_1:227_bsr=unit_only:slsqr=307,512:sas=z3:plsq=on:plsqc=1:avsqr=97,32:plsqr=27942579,963352:slsql=off:sp=occurrence:abs=on:drc=off:plsql=on:awrs=converge:fd=preordered:slsq=on:slsqc=1:avsqc=1:amm=off:avsq=on:st=3.0:awrsf=256:ss=axioms:i=14400:i=6563_0");
    quick.push("lrs+1002_1:1024_slsqr=1,8:drc=off:urr=on:uwa=all:nwc=5.0:slsqc=1:slsq=on:i=4440:ins=1:slsql=off:i=3609_0");
    quick.push("ott+10_1:1_si=on:rtra=on:rawr=on:slsqr=55,52:drc=off:plsq=on:plsqc=1:sp=occurrence:uwa=one_side_interpreted:fd=off:nwc=4.0:thsql=off:slsq=on:i=17760:thsqd=16:thsqc=16:thsq=on:slsql=off:i=3943_0");
    quick.push("dis+1011_1:32_tgt=ground:i=100000:i=54993_0");
    quick.push("ott+10_1:1_sp=reverse_frequency:drc=off:bd=preordered:fd=preordered:nwc=5.0:i=18840:i=11923_0");
    quick.push("lrs+10_3:1_fde=none:lwlo=on:i=26400:bd=off:i=13822_0");
    quick.push("lrs+10_1:128_to=lpo:drc=off:sp=reverse_frequency:i=26040:awrs=converge:bd=preordered:i=14361_0");
    quick.push("lrs+10_1:1024_to=lpo:tgt=full:drc=off:sp=unary_frequency:i=100000:i=38568_0");
    quick.push("dis+20_1:12_to=lpo:spb=goal:acc=model:fd=preordered:nwc=3.0:s2agt=16:nicw=on:s2a=on:i=100000:aac=none:awrs=converge:fsr=off:i=8358_0");
    quick.push("lrs+21_1:14_sfv=off:tgt=ground:drc=off:urr=on:br=off:tha=off:s2a=on:i=40000:awrs=converge:ev=cautious:i=30413_0");
    quick.push("ott+10_2:217_avsqr=5,12:drc=off:awrs=decay:nwc=3.0:avsq=on:st=2.0:avsql=on:bs=on:awrsf=3:ss=axioms:i=67200:i=8865_0");
    quick.push("dis+1011_1:1_urr=on:nwc=2.0:mep=off:i=59280:ep=RSTC:av=off:gsp=on:i=10455_0");
    quick.push("dis+1010_1:10_tgt=ground:fde=unused:i=40000:fsr=off:i=13638_0");
    quick.push("lrs+33_1:4_si=on:rtra=on:rawr=on:tgt=ground:lwlo=on:s2a=on:i=40000:i=33190_0");
    quick.push("lrs+2_1:128_si=on:rtra=on:rawr=on:drc=off:spb=units:thsqr=4,7:nwc=1.94:lwlo=on:i=287832:thsqd=32:awrs=decay:awrsf=20:fsd=on:nm=2:thsqc=32:thsq=on:i=283858_0");
    quick.push("ott+10_13:991_si=on:rtra=on:rawr=on:drc=off:sp=const_frequency:spb=goal_then_units:uwa=all:fd=preordered:i=209700:awrs=decay:awrsf=1:bd=preordered:i=22569_0");
    quick.push("lrs+1011_1:1_to=lpo:drc=off:sp=reverse_arity:uwa=one_side_interpreted:fd=preordered:gs=on:nwc=10.0:s2a=on:bs=on:i=73440:add=large:ins=1:bd=off:i=57383_0");
    quick.push("lrs+10_1:5_drc=off:thi=neg_eq:plsq=on:plsqr=32,1:plsql=on:fd=preordered:gs=on:newcnf=on:lwlo=on:bs=unit_only:i=145707:av=off:i=35764_0");
    quick.push("lrs+11_13918:311883_drc=off:sas=z3:etr=on:atotf=0.1:fd=preordered:nwc=5.0:s2agt=32:nicw=on:s2a=on:i=43320:awrs=decay:er=filter:i=35773_0");
    quick.push("ott+11_1:1024_tgt=full:drc=off:plsq=on:spb=goal:kmz=on:i=107400:bs=on:kws=precedence:bd=off:i=79227_0");
    quick.push("dis+10_1:1024_tgt=full:drc=off:fd=preordered:s2a=on:i=100000:i=68813_0");
    quick.push("ott+10_1:1024_anc=all:to=lpo:drc=off:sos=on:sac=on:bs=unit_only:i=172200:afp=20:bd=preordered:afq=2.0:i=81553_0");
    quick.push("ott+10_1:128_anc=all_dependent:to=lpo:drc=off:urr=on:uwa=interpreted_only:nwc=5.0:st=5.0:avsq=on:avsqr=117,34:i=229440:afp=10:aac=none:awrs=converge:ins=1:bd=preordered:ss=axioms:i=86505_0");
    quick.push("lrs+10_1:14_to=lpo:drc=off:nwc=10.0:i=143160:i=107231_0");
    quick.push("ott+4_1:1_sp=frequency:spb=units:bce=on:atotf=0.5:i=300720:ins=1:i=160557_0");
    quick.push("dis+1011_1:64_slsqr=17,16:tgt=full:plsq=on:plsqc=1:bsd=on:plsqr=37,6:foolp=on:bce=on:nwc=2.0:s2agt=32:slsqc=1:flr=on:slsq=on:cond=on:i=336750:slsql=off:av=off:bd=off:i=273601_0");
  } else if (property.category() == Property::Category::FNE || property.category() == Property::Category::FEQ) {
    // FOF
    quick.push("lrs+10_1:1_i=10440:ss=included:i=23_0");
    quick.push("lrs+10_5:1_fde=none:sos=on:urr=on:nwc=3.0:sd=1:br=off:ss=axioms:sgt=10:i=4440:i=2436_0");
    quick.push("dis+1011_1:1_nwc=3.0:i=40000:aac=none:er=known:i=7559_0");
    quick.push("lrs+10_1:1_to=lpo:sos=on:ep=RS:ss=axioms:i=240:i=4_0");
    quick.push("dis+1010_1:1024_to=lpo:sp=frequency:sos=on:fd=off:aac=none:ss=axioms:i=120:i=17_0");
    quick.push("lrs+10_1:1_sos=all:lma=on:spb=goal:lcm=predicate:i=21240:ep=R:ss=included:i=27_0");
    quick.push("dis+10_1:1_plsq=on:plsqr=2,7:erd=off:urr=on:br=off:nwc=10.0:s2agt=8:newcnf=on:s2a=on:i=360:i=56_0");
    quick.push("dis+1010_1:50_sp=frequency:awrs=decay:nwc=10.0:s2pl=no:awrsf=128:ss=axioms:i=360:i=189_0");
    quick.push("lrs+2_1:4_urr=on:br=off:i=6480:sd=2:ss=included:i=79_0");
    quick.push("lrs+10_1:1_to=lpo:drc=off:sp=reverse_frequency:spb=goal:i=120:i=88_0");
    quick.push("lrs+1004_1:1_sos=all:i=120:av=off:bd=off:i=77_0");
    quick.push("lrs+1010_1:4_sos=on:bce=on:amm=off:sd=1:ss=included:i=240:i=76_0");
    quick.push("lrs+35_1:4_bsr=unit_only:slsqr=1,2:sp=frequency:lcm=reverse:slsqc=1:flr=on:slsq=on:i=409:av=off:slsql=off:i=355_0");
    quick.push("lrs+10_1:16_slsqr=1,2:plsq=on:fde=none:plsqr=32,1:sos=all:nwc=3.0:slsqc=0:slsq=on:i=240:sd=1:ep=R:ss=axioms:si=on:rtra=on:rawr=on:i=16_0");
    quick.push("lrs+10_1:1_nwc=3.0:i=2040:ss=included:sgt=8:i=423_0");
    quick.push("ott+1011_101:499_si=on:rtra=on:rawr=on:bsr=unit_only:drc=off:sp=occurrence:sos=on:thsqr=2,9:acc=on:fd=preordered:nwc=2.0:alpa=false:sac=on:nicw=on:i=101040:afp=175:aac=none:thsqd=32:awrs=converge:awrsf=7:fsd=on:amm=sco:thsqc=32:afq=1.384:thsq=on:i=45_0");
    quick.push("fmb+10_1:1_i=120:nm=2:i=72_0");
    quick.push("dis+1002_1:1_to=lpo:spb=goal_then_units:nwc=2.0:s2a=on:i=120:nm=0:i=80_0");
    quick.push("lrs+1011_1:1_sos=on:uwa=ground:fd=preordered:i=596:thsqd=32:fsd=on:thsqc=64:thsq=on:i=546_0");
    quick.push("dis+1002_1:1_sos=on:sac=on:newcnf=on:nicw=on:aac=none:i=360:i=90_0");
    quick.push("lrs+11_1:28_to=lpo:irw=on:fde=unused:uwa=all:slsqc=1:slsq=on:i=213:ins=2:av=off:bd=preordered:i=19_0");
    quick.push("dis+21_1:1_nwc=10.0:s2a=on:i=120:s2at=1.5:ep=RS:i=59_0");
    quick.push("dis+10_1:1_anc=all:bsr=unit_only:plsq=on:fde=unused:to=lpo:add=off:plsqr=23,8:sp=frequency:sos=all:erd=off:spb=goal:bd=off:nwc=5.0:sac=on:nicw=on:aac=none:ins=1:rnwc=on:i=1320:i=5_0");
    quick.push("lrs+1010_1:1_sos=on:bd=off:sd=1:ss=axioms:fsr=off:i=240:i=21_0");
    quick.push("ott+10_1:1_drc=off:sp=frequency:sos=on:urr=on:flr=on:i=298:av=off:fsr=off:i=42_0");
    quick.push("lrs+1010_1:1_to=lpo:fde=none:sos=on:spb=goal:fd=off:sac=on:i=480:ins=3:bd=off:i=334_0");
    quick.push("lrs+10_1:32_urr=on:br=off:st=2.0:i=240:sd=2:nm=16:ss=axioms:i=120_0");
    quick.push("lrs+2_1:1_sos=all:lma=on:spb=goal_then_units:urr=on:lcm=reverse:ss=included:i=240:i=62_0");
    quick.push("dis+1002_1:12_tgt=full:drc=off:fd=preordered:i=100000:i=98261_0");
    quick.push("ott+1011_3:1_to=lpo:spb=goal:urr=on:s2a=on:i=360:s2at=2.0:nm=0:i=285_0");
    quick.push("lrs+10_1:1_i=24000:ss=axioms:sgt=8:i=5072_0");
    quick.push("lrs+11_1:1_si=on:rtra=on:rawr=on:to=lpo:sp=reverse_arity:sos=on:urr=on:br=off:fd=preordered:i=360:i=319_0");
    quick.push("lrs+1010_1:1_sos=on:ep=RS:i=120:i=34_0");
    quick.push("lrs+1011_1:2_plsq=on:plsqc=1:plsqr=15,8:acc=on:avsqc=2:avsq=on:avsqr=1,16:i=120:awrs=converge:i=94_0");
    quick.push("dis+2_3:1_sp=const_frequency:sos=on:spb=units:abs=on:urr=ec_only:lcm=reverse:nwc=10.0:i=720:aac=none:ep=R:i=28_0");
    quick.push("lrs+10_1:8_si=on:rtra=on:rawr=on:sos=on:urr=on:rnwc=on:nwc=5.0:i=77160:ep=R:i=47_0");
    quick.push("lrs+1010_1:1_to=lpo:sp=frequency:sos=on:i=960:sd=1:ss=included:i=444_0");
    quick.push("dis+1011_1:128_bs=unit_only:ep=RS:ss=axioms:av=off:i=240:i=10_0");
    quick.push("dis+1003_1:128_to=lpo:tgt=full:sp=unary_frequency:nwc=5.0:s2a=on:i=40000:av=off:i=10_0");
    quick.push("lrs+10_1:1_sos=on:urr=on:bce=on:i=27960:sd=1:ep=RST:gsp=on:ss=axioms:i=61_0");
    quick.push("dis+21_1:1_sp=frequency:lcm=predicate:nwc=3.0:i=120:aac=none:er=known:i=11_0");
    quick.push("dis+1011_1:32_plsq=on:fde=unused:plsqc=2:to=lpo:plsqr=175,8:sp=frequency:spb=goal:bd=off:st=2.0:s2a=on:ss=included:i=1080:i=488_0");
    quick.push("dis+1002_1:1_to=lpo:sos=on:sd=1:ss=axioms:ins=1:i=14760:i=929_0");
    quick.push("dis+21_1:8_fd=off:nwc=5.0:s2pl=no:bs=unit_only:i=120:aac=none:er=filter:i=12_0");
    quick.push("ott+10_1:1_anc=all_dependent:sp=unary_frequency:spb=non_intro:acc=on:urr=on:tha=off:fd=preordered:sac=on:newcnf=on:i=3600:canc=force:i=12_0");
    quick.push("lrs+2_1:1_fde=none:sos=on:nwc=5.0:lcm=reverse:ep=R:i=120:i=24_0");
    quick.push("dis+10_1:1_slsqr=1,4:fde=none:slsqc=1:slsq=on:i=240:slsql=off:ep=R:fsr=off:ss=axioms:i=155_0");
    quick.push("ott+10_4:7_to=lpo:sp=reverse_frequency:sos=on:urr=on:bd=preordered:awrs=converge:nwc=10.0:flr=on:i=9240:i=13_0");
    quick.push("dis+1011_1:1_slsqr=4,15:fde=unused:slsq=on:nwc=10.0:slsqc=1:av=off:er=known:i=120:i=91_0");
    quick.push("dis+1011_1:145_si=on:rtra=on:rawr=on:slsqr=5,3:irw=on:plsq=on:add=large:avsqr=209,123:plsqr=1,6:sos=on:erd=off:spb=goal_then_units:bd=off:atotf=0.5:plsql=on:awrs=decay:slsq=on:nwc=2.0:slsqc=0:alpa=true:skr=on:avsqc=1:newcnf=on:nicw=on:amm=sco:avsq=on:bs=on:awrsf=89:fsd=on:nm=0:afr=on:i=6360:i=383_0");
    quick.push("lrs+10_1:64_plsq=on:plsqr=32,1:sos=all:sac=on:st=5.0:i=240:ss=axioms:i=153_0");
    quick.push("lrs+10_1:1_to=lpo:fde=unused:sp=reverse_arity:sos=on:spb=goal_then_units:urr=ec_only:lcm=reverse:avsq=on:avsqr=1,16:i=2640:bd=off:i=15_0");
    quick.push("lrs+11_1:32_to=lpo:drc=off:fd=preordered:flr=on:i=469:awrs=converge:awrsf=32:bd=preordered:i=420_0");
    quick.push("lrs+10_1:1024_nwc=5.0:ss=axioms:nm=0:i=120:i=18_0");
    quick.push("lrs+10_1:1_sos=on:st=1.5:sd=2:ss=axioms:av=off:i=1560:i=258_0");
    quick.push("dis+1011_1:1_slsqr=12,59:sp=reverse_arity:abs=on:rnwc=on:nwc=4.0:thsql=off:skr=on:slsq=on:cond=fast:s2a=on:bs=unit_only:i=1080:s2at=3.6:add=off:aac=none:thsqd=32:ep=RS:thsqc=64:gsp=on:thsq=on:i=385_0");
    quick.push("lrs+21_1:16_sp=frequency:spb=goal_then_units:lcm=reverse:i=240:sd=2:gsp=on:ss=included:i=106_0");
    quick.push("lrs+1011_1:4_to=lpo:tgt=full:drc=off:spb=goal:nwc=2.0:i=40000:ins=1:av=off:bd=off:i=29649_0");
    quick.push("lrs+10_1:1_sos=on:urr=on:s2agt=16:s2a=on:i=5160:sd=1:ss=included:i=4416_0");
    quick.push("dis+1011_1:1_spb=goal_then_units:urr=ec_only:nm=0:gs=on:i=15000:i=203_0");
    quick.push("ott+1011_1:2_bsr=unit_only:urr=on:s2agt=32:nwc=5.0:s2a=on:bs=unit_only:br=off:i=20160:i=14500_0");
    quick.push("dis+21_1:1_to=lpo:sp=frequency:sos=on:ss=included:av=off:i=240:i=143_0");
    quick.push("dis+1011_1:64_slsqr=17,16:tgt=full:plsq=on:plsqc=1:bsd=on:plsqr=37,6:foolp=on:bce=on:nwc=2.0:s2agt=32:slsqc=1:flr=on:slsq=on:cond=on:i=336750:slsql=off:av=off:bd=off:i=296767_0");
    quick.push("dis+1010_1:4_slsqr=3,2:atotf=0.3:nwc=5.0:slsqc=1:slsq=on:s2a=on:i=300:s2at=5.0:fsr=off:i=135_0");
    quick.push("dis+1002_1:1_slsqr=1,8:nwc=10.0:slsqc=0:mep=off:newcnf=on:slsq=on:dr=on:s2a=on:i=28800:ep=RS:nm=2:av=off:i=17042_0");
    quick.push("lrs+10_1:2_to=lpo:drc=off:plsq=on:sp=reverse_frequency:sac=on:i=240:ins=3:i=23_0");
    quick.push("lrs+10_1:32_urr=on:br=off:nwc=5.0:i=240:nm=6:gsp=on:i=50_0");
    quick.push("dis+10_1:1_to=lpo:sp=reverse_arity:sos=on:urr=ec_only:st=2.0:ss=included:av=off:i=2040:i=720_0");
    quick.push("dis+10_1:4_si=on:rtra=on:rawr=on:anc=none:sos=on:erd=off:urr=on:avsq=on:ep=RS:ins=1:gs=on:i=8280:i=55_0");
    quick.push("dis+1003_1:128_urr=on:bce=on:atotf=0.5:newcnf=on:i=120:i=86_0");
    quick.push("dis+1011_1:1_si=on:rtra=on:rawr=on:fde=unused:to=lpo:sp=reverse_frequency:sos=on:spb=goal:bd=off:fd=preordered:sfv=off:i=1800:i=271_0");
    quick.push("dis+32_1:1_sos=on:i=240:nm=4:bd=off:ss=included:i=90_0");
    quick.push("lrs+10_1:1_sos=on:nwc=10.0:st=3.0:lcm=reverse:aac=none:ss=axioms:i=240:i=35_0");
    quick.push("ott+10_1:1_bsr=unit_only:sp=frequency:cond=on:i=22920:sd=1:nm=16:ss=included:i=108_0");
    quick.push("ott+10_1:1_fde=unused:to=lpo:sos=all:urr=on:fd=off:st=2.0:s2a=on:sd=2:br=off:ss=axioms:i=23880:i=8816_0");
    quick.push("lrs+1011_74:79_slsqr=1,1:to=lpo:drc=off:pum=on:norm_ineq=on:sims=off:ile=on:gve=force:spb=goal:atotf=0.1:uwa=all:nwc=5.0:slsqc=1:updr=off:slsq=on:nicw=on:bs=unit_only:i=120:add=off:aac=none:afq=1.0:tac=rule:afr=on:gsp=on:i=112_0");
    quick.push("lrs+10_1:32_slsqr=1,2:to=lpo:drc=off:sos=on:fd=preordered:slsqc=0:slsq=on:i=600:awrs=converge:awrsf=20:i=209_0");
    quick.push("dis+1011_1:1_slsqr=1,8:rnwc=on:nwc=5.0:slsqc=2:slsq=on:s2a=on:bs=unit_only:i=2760:s2at=3.0:aac=none:ep=RS:gsp=on:i=2038_0");
    quick.push("lrs+10_1:1_sos=on:i=11640:sd=1:ss=included:i=7481_0");
    quick.push("dis+10_1:7_to=lpo:drc=off:plsq=on:sp=reverse_frequency:fd=preordered:i=360:i=91_0");
    quick.push("lrs+1002_1:7_sos=on:i=2280:i=1780_0");
    quick.push("ott+10_1:1_bsr=unit_only:fde=none:sos=all:fd=off:nwc=3.0:i=1080:av=off:bd=off:i=96_0");
    quick.push("dis+1010_1:4_si=on:rtra=on:rawr=on:tgt=ground:fde=none:bsd=on:sas=z3:sp=const_min:gve=cautious:erd=off:abs=on:thsqr=1,4:atotf=0.5:rnwc=on:nwc=5.0:avsqc=2:sac=on:newcnf=on:avsq=on:avsqr=215,247:i=40000:aac=none:awrs=converge:awrsf=128:thsqc=64:thsq=on:i=13789_0");
    quick.push("dis+2_1:1_slsqr=1,16:slsqc=1:flr=on:slsq=on:s2a=on:i=240:er=known:slsql=off:i=50_0");
    quick.push("dis+10_1:4_urr=ec_only:br=off:i=600:i=302_0");
    quick.push("dis+10_1:128_sos=on:st=3.0:i=10320:sd=2:ss=axioms:i=1211_0");
    quick.push("lrs+1002_1:1_bsr=on:slsqr=292,253:fde=none:to=lpo:sims=off:etr=on:sp=frequency:drc=off:urr=ec_only:slsq=on:nwc=10.0:slsqc=0:newcnf=on:st=1.5:s2a=on:bs=on:ss=axioms:fsd=on:av=off:fsr=off:gs=on:fsdmm=1:i=3000:i=51_0");
    quick.push("lrs+1011_5:1_slsqr=5,4:fde=none:sos=all:slsq=on:i=240:ep=R:fsr=off:slsql=off:i=51_0");
    quick.push("dis+10_1:1_newcnf=on:lcm=reverse:s2a=on:s2at=3.0:ep=RS:av=off:i=4320:i=2332_0");
    quick.push("lrs+1011_1:16_tgt=ground:drc=off:s2a=on:i=40000:bd=preordered:i=6391_0");
    quick.push("dis+10_1:24_si=on:rtra=on:rawr=on:to=lpo:drc=off:urr=on:br=off:i=30960:av=off:er=known:i=58_0");
    quick.push("dis+1010_1:1024_bsr=on:fde=unused:bce=on:gs=on:nwc=3.0:skr=on:s2a=on:i=840:awrs=converge:awrsf=256:ins=1:av=off:i=358_0");
    quick.push("lrs+1002_1:64_plsq=on:sos=on:i=240:av=off:bd=off:gsp=on:i=121_0");
    quick.push("dis+10_1:1_si=on:rtra=on:rawr=on:slsqr=1,4:bsd=on:nwc=5.0:slsqc=2:slsq=on:i=10000:slsql=off:fsd=on:i=61_0");
    quick.push("dis+10_5:1_to=lpo:drc=off:sp=reverse_arity:sos=all:spb=goal:i=240:i=187_0");
    quick.push("lrs+11_1:1_st=1.5:i=70560:ss=included:i=49329_0");
    quick.push("lrs+1011_1:1_si=on:rtra=on:rawr=on:slsqr=1,8:tgt=full:foolp=on:urr=ec_only:uwa=all:fd=preordered:gs=on:nwc=5.0:slsqc=1:slsq=on:i=100000:s2at=4.2:av=off:er=known:i=66127_0");
    quick.push("lrs+10_1:1_sfv=off:plsq=on:plsqc=2:etr=on:sp=frequency:sos=all:urr=on:plsql=on:br=off:sac=on:newcnf=on:s2a=on:bs=on:i=7080:s2at=3.0:sd=2:fsd=on:amm=off:ss=axioms:i=5395_0");
    quick.push("lrs+1011_1:128_plsq=on:to=lpo:bd=off:av=off:i=600:i=340_0");
    quick.push("lrs+0_1:1_drc=off:erd=off:urr=ec_only:br=off:i=1080:i=696_0");
    quick.push("dis+21_1:1_slsqr=1,1:to=lpo:sp=frequency:slsq=on:slsqc=0:av=off:er=filter:i=120:i=70_0");
    quick.push("dis+1010_1:3_si=on:rtra=on:rawr=on:bsr=on:slsqr=1,4:uwa=all:slsqc=1:slsq=on:cond=on:bs=on:i=360:av=off:bd=off:gsp=on:i=70_0");
    quick.push("dis+1011_1:32_nwc=5.0:s2a=on:er=filter:i=120:i=74_0");
    quick.push("ott+10_1:50_anc=all:slsqr=17,16:plsq=on:to=lpo:avsqr=9,8:plsqr=32,1:slsql=off:drc=off:plsql=on:fd=preordered:slsq=on:nwc=5.0:slsqc=1:sac=on:avsq=on:st=2.4:avsql=on:bs=unit_only:ss=included:ins=2:sgt=4:i=17400:i=75_0");
    quick.push("lrs+10_1:4_to=lpo:sp=frequency:drc=off:i=1200:i=1168_0");
    quick.push("dis+10_1:1_bsr=unit_only:sfv=off:slsqr=3,2:drc=off:plsq=on:plsqc=1:plsqr=232,15:sp=weighted_frequency:sos=on:gve=cautious:abs=on:bce=on:lcm=reverse:fd=preordered:slsq=on:i=2520:aac=none:fsd=on:nm=16:bd=off:slsql=off:i=82_0");
    quick.push("lrs+1004_1:3_bsr=unit_only:to=lpo:fde=none:etr=on:sos=all:fd=preordered:slsq=on:i=2880:thsqd=32:ins=1:fsd=on:av=off:thsqc=64:thsq=on:slsql=off:i=169_0");
    quick.push("dis+1004_1:1_urr=ec_only:br=off:i=240:fsd=on:i=86_0");
    quick.push("lrs+1011_1:1_sos=on:spb=units:i=244320:ep=R:nm=0:gsp=on:ss=included:i=128061_0");
    quick.push("lrs+1002_1:1_fde=none:sos=on:abs=on:acc=on:urr=on:nwc=5.0:avsqc=1:newcnf=on:nicw=on:avsq=on:avsqr=7,8:bs=on:i=480:i=92_0");
    quick.push("dis+20_1:12_to=lpo:spb=goal:acc=model:fd=preordered:nwc=3.0:s2agt=16:nicw=on:s2a=on:i=100000:aac=none:awrs=converge:fsr=off:i=8255_0");
    quick.push("lrs+21_1:1_i=40000:kws=precedence:fsr=off:i=961_0");
    quick.push("lrs+1010_1:1_fde=unused:sos=on:st=1.5:ss=axioms:i=3360:i=97_0");
    quick.push("dis+1010_1:16_nicw=on:ss=included:fsd=on:i=720:i=293_0");
    quick.push("lrs+10_1:1_anc=all:urr=on:br=off:sac=on:newcnf=on:s2a=on:i=165120:s2at=2.0:sd=1:ss=included:i=34407_0");
    quick.push("dis+1010_1:1_fde=none:newcnf=on:s2a=on:fsr=off:i=240:i=102_0");
    quick.push("lrs+1004_1:1024_sos=all:urr=on:atotf=0.3:i=240:ep=RS:i=104_0");
    quick.push("lrs+1010_1:6_bsr=on:slsqr=1,1:irw=on:fde=unused:to=lpo:sims=off:add=large:sp=occurrence:drc=off:acc=on:urr=ec_only:bd=off:slsq=on:nwc=3.0:slsqc=0:alpa=false:skr=on:sac=on:newcnf=on:nicw=on:st=3.0:bs=on:sd=1:afp=9:ss=axioms:fsd=on:aer=off:afq=1.4:fsdmm=2:i=240:i=210_0");
    quick.push("dis+1010_1:1024_newcnf=on:fsr=off:i=360:i=215_0");
    quick.push("lrs+11_1:1_newcnf=on:i=240:sd=2:fsr=off:ss=axioms:i=109_0");
    quick.push("lrs+10_1:1_to=lpo:tgt=ground:sp=const_frequency:slsq=on:i=40000:bd=preordered:i=780_0");
    quick.push("lrs+10_1:1_sos=all:st=4.0:i=60000:sd=10:av=off:ss=axioms:i=224_0");
    quick.push("lrs+1011_1:7_bsr=on:to=lpo:sp=reverse_frequency:urr=on:fd=preordered:nwc=5.0:s2a=on:i=720:s2at=2.0:av=off:i=113_0");
    quick.push("dis+11_1:1_bce=on:bs=on:i=240:ep=RST:nm=0:av=off:gsp=on:ss=included:i=118_0");
    quick.push("dis+1002_1:1_anc=all:flr=on:sac=on:s2a=on:sd=2:ep=R:ss=axioms:i=3360:i=129_0");
    quick.push("ott+10_1:50_bsr=unit_only:sp=frequency:drc=off:fd=preordered:i=21840:i=1634_0");
    quick.push("lrs+10_1:1_to=lpo:sp=frequency:sos=all:lma=on:abs=on:drc=off:sac=on:sfv=off:i=600:i=276_0");
    quick.push("dis+10_1:1_si=on:rtra=on:rawr=on:plsq=on:plsqr=32,1:sos=all:newcnf=on:st=3.0:sd=1:ss=included:nm=2:av=off:gs=on:i=3000:i=764_0");
    quick.push("lrs+4_1:32_to=lpo:sp=frequency:i=7440:i=3417_0");
    quick.push("dis+1002_1:1_fde=unused:nwc=10.0:sac=on:s2a=on:i=45360:s2at=3.0:i=31451_0");
    quick.push("ott+1004_1:1_si=on:rtra=on:rawr=on:anc=all_dependent:bsr=on:slsqr=1,4:to=lpo:slsql=off:sp=reverse_arity:spb=goal_then_units:urr=on:slsq=on:nwc=3.0:slsqc=0:sac=on:s2a=on:s2at=2.0:gs=on:i=2880:i=534_0");
    quick.push("lrs+1002_1:1_si=on:rtra=on:rawr=on:plsq=on:plsqc=1:plsqr=32,1:atotf=0.3:plsql=on:cond=on:avsq=on:avsqr=55,124:i=840:nm=3:i=152_0");
    quick.push("lrs+10_1:128_sos=all:st=2.0:sd=1:ep=RS:ss=axioms:av=off:i=5520:i=919_0");
    quick.push("lrs+10_1:8_tgt=ground:nwc=2.0:i=40000:i=326_0");
    quick.push("lrs+10_1:1_sos=on:urr=on:st=2.0:br=off:ss=axioms:i=2760:i=1776_0");
    quick.push("lrs+10_1:1_to=lpo:spb=goal_then_units:drc=off:bd=off:nwc=5.0:lcm=reverse:sd=1:ss=axioms:sgt=16:i=480:i=167_0");
    quick.push("lrs+10_1:4_to=lpo:drc=off:sos=on:i=573:i=334_0");
    quick.push("lrs+1011_45163:73544_anc=none:bsr=unit_only:slsqr=59173,778640:fde=unused:sp=occurrence:abs=on:nwc=4.0:slsqc=2:alpa=false:skr=on:updr=off:mep=off:slsq=on:cond=fast:avsq=on:avsqr=57,253:bs=on:i=37080:add=large:aac=none:ep=R:amm=off:afr=on:gsp=on:slsql=off:i=16442_0");
    quick.push("lrs+10_1:2_to=lpo:drc=off:plsq=on:plsqc=1:erd=off:urr=on:plsql=on:uace=off:nwc=10.0:lwlo=on:s2a=on:i=234:s2at=5.0:aac=none:fsr=off:i=175_0");
    quick.push("lrs+10_1:1_to=lpo:sp=reverse_arity:sos=on:i=26640:sd=2:av=off:ss=axioms:i=7162_0");
    quick.push("lrs+10_1:1_sos=on:urr=on:st=1.2:i=420720:ss=included:i=160871_0");
    quick.push("lrs+1011_1:1_plsq=on:plsqr=1,32:sp=occurrence:sos=on:acc=model:plsql=on:gs=on:skr=on:flr=on:updr=off:sac=on:newcnf=on:avsq=on:s2a=on:i=3480:s2at=3.0:fsd=on:bd=off:i=185_0");
    quick.push("ott+10_13:991_si=on:rtra=on:rawr=on:bsr=on:drc=off:sp=const_frequency:spb=goal_then_units:fd=preordered:bs=on:i=47640:awrs=decay:awrsf=1:bd=off:i=372_0");
    quick.push("dis+1011_2388710:563463_sp=frequency:erd=off:fs=off:bce=on:ep=RS:fsr=off:i=12360:i=1642_0");
    quick.push("lrs+10_1:7_plsq=on:plsqc=1:to=lpo:bsd=on:drc=off:urr=on:awrs=converge:s2agt=16:nwc=3.0:cond=on:s2a=on:awrsf=40:br=off:av=off:i=1080:i=622_0");
    quick.push("lrs+10_1:16_fde=none:sos=on:urr=on:br=off:nwc=3.0:i=480:ins=1:ss=axioms:i=186_0");
    quick.push("lrs+1011_1:64_nwc=3.0:s2a=on:sd=1:ss=included:sgt=64:i=240:i=190_0");
    quick.push("ott+32_8:1_to=lpo:drc=off:foolp=on:spb=goal_then_units:nwc=10.0:s2agt=8:thsql=off:flr=on:dr=on:cond=fast:s2a=on:i=8280:thsqd=16:nm=16:av=off:thsqc=64:thsq=on:i=193_0");
    quick.push("dis+1002_1:28_si=on:rtra=on:rawr=on:nwc=5.0:s2a=on:i=12840:s2at=3.0:av=off:i=205_0");
    quick.push("dis+21_1:1_to=lpo:spb=goal_then_units:nwc=5.0:s2a=on:s2at=2.2:av=off:i=480:i=410_0");
    quick.push("dis+10_1:1_to=lpo:sos=all:lma=on:spb=goal_then_units:sac=on:ss=axioms:i=720:i=413_0");
    quick.push("ott+10_1:1_si=on:rtra=on:rawr=on:fde=none:flr=on:s2a=on:i=3240:i=210_0");
    quick.push("lrs+10_1:3_slsqr=1,4:plsq=on:plsqr=3423,254:urr=on:plsql=on:br=off:nwc=5.0:slsqc=2:slsq=on:lwlo=on:s2a=on:i=34920:gsp=on:slsql=off:i=17218_0");
    quick.push("lrs+11_1:128_plsq=on:plsqc=1:to=lpo:avsqr=1,16:plsqr=65,12:sos=on:spb=goal_then_units:urr=on:awrs=converge:avsqc=2:avsq=on:avsql=on:bs=on:aac=none:nm=0:i=1680:i=833_0");
    quick.push("lrs+21_1:8_slsqr=1,4:to=lpo:tgt=ground:drc=off:urr=on:nwc=10.0:flr=on:slsq=on:lwlo=on:i=40000:bs=unit_only:av=off:i=13477_0");
    quick.push("dis+10_1:1_to=lpo:sos=on:urr=on:newcnf=on:ss=axioms:sgt=8:i=720:i=439_0");
    quick.push("dis+1010_1:1_to=lpo:sp=reverse_frequency:acc=model:nwc=5.0:i=480:ins=1:bd=off:i=221_0");
    quick.push("lrs+10_1:1_anc=all_dependent:bsr=unit_only:fde=unused:sos=all:spb=goal_then_units:nwc=5.0:skr=on:cond=fast:st=2.0:aac=none:ss=axioms:fsr=off:i=960:i=443_0");
    quick.push("lrs+10_1:1_sos=all:urr=ec_only:i=28440:sd=1:ss=axioms:i=225_0");
    quick.push("lrs+10_1:2_to=lpo:sp=const_frequency:sos=on:urr=on:br=off:fd=off:i=638:ins=3:fsr=off:bd=off:i=233_0");
    quick.push("lrs+10_1:1_sos=on:urr=on:br=off:i=27480:sd=1:ss=axioms:sgt=8:i=9480_0");
    quick.push("dis+1002_1:4_newcnf=on:i=19320:ep=RST:av=off:i=9366_0");
    quick.push("lrs+10_1:64_to=lpo:bd=off:fd=preordered:flr=on:nicw=on:fsr=off:i=2040:i=1907_0");
    quick.push("lrs+1002_1:1_sos=on:st=3.0:s2a=on:i=4440:sd=2:ss=included:i=3312_0");
    quick.push("lrs+1010_10:13_anc=none:bsr=on:to=lpo:drc=off:sas=z3:fde=none:sims=off:sp=frequency:sos=on:spb=units:abs=on:urr=on:lcm=reverse:fd=preordered:gs=on:nwc=5.0:skr=on:flr=on:avsqc=1:updr=off:gsem=off:cond=on:avsq=on:avsqr=12,23:i=5160:gsaa=full_model:ins=3:fsr=off:amm=off:i=861_0");
    quick.push("dis+1011_1:1_avsqr=1,16:spb=units:nwc=5.0:avsqc=2:sac=on:avsq=on:avsql=on:i=600:i=294_0");
    quick.push("lrs+10_1:1024_si=on:rtra=on:rawr=on:bsr=on:tgt=ground:drc=off:uwa=ground:fd=preordered:i=40000:thsqd=32:awrs=converge:awrsf=60:bd=off:thsqc=8:thsq=on:i=302_0");
    quick.push("dis+1002_1:1_sos=on:erd=off:sac=on:i=3600:ep=RS:i=1613_0");
    quick.push("dis+1011_1:1_si=on:rtra=on:rawr=on:bsr=on:sas=z3:plsq=on:plsqc=1:plsqr=107,4:sp=reverse_frequency:erd=off:spb=units:nwc=5.0:updr=off:s2a=on:s2at=1.5:i=1680:i=985_0");
    quick.push("dis+1011_1:10_bsd=on:bce=on:nwc=2.0:i=1920:awrs=decay:av=off:bd=off:i=1755_0");
    quick.push("dis+1010_5:1_sas=z3:fde=unused:sp=reverse_frequency:abs=on:nwc=10.0:s2a=on:i=3840:s2at=1.5:ep=RST:ins=1:gsp=on:i=668_0");
    quick.push("ott+1011_1:1_si=on:rtra=on:rawr=on:anc=all:bsr=unit_only:erd=off:fs=off:drc=off:urr=on:nwc=3.0:avsqc=1:sac=on:avsq=on:s2a=on:s2at=1.5:fsr=off:i=6240:i=336_0");
    quick.push("dis+1011_2:3_si=on:rtra=on:rawr=on:anc=none:bsr=on:slsqr=1,8:fde=unused:sp=unary_frequency:spb=goal:abs=on:nwc=3.0:slsqc=2:alpa=true:skr=on:slsq=on:cond=fast:avsq=on:avsqr=9,40:i=3840:aac=none:ep=R:amm=off:slsql=off:i=2492_0");
    quick.push("lrs+10_1:1_sos=on:sd=2:ss=axioms:i=15000:i=7505_0");
    quick.push("ott+10_1:1_slsqr=10,31:to=lpo:tgt=ground:drc=off:fde=unused:sp=const_min:urr=ec_only:slsq=on:i=40000:bd=preordered:i=15381_0");
    quick.push("dis+10_1:1_slsqr=1,1:to=lpo:sp=frequency:erd=off:spb=goal_then_units:slsqc=0:slsq=on:i=15240:ep=R:av=off:gsp=on:i=343_0");
    quick.push("lrs+1011_1:1024_slsqr=1,8:urr=ec_only:br=off:slsqc=2:slsq=on:i=1200:s2at=3.0:av=off:slsql=off:i=686_0");
    quick.push("dis+10_1:50_to=lpo:drc=off:i=3960:i=2888_0");
    quick.push("lrs+1011_4:7_slsqr=1,8:sas=z3:plsq=on:plsqr=1,2:sp=frequency:bce=on:plsql=on:slsqc=0:skr=on:flr=on:newcnf=on:slsq=on:cond=on:st=1.2:i=12000:awrs=decay:awrsf=8:afr=on:ss=axioms:slsql=off:i=1768_0");
    quick.push("lrs+10_1:1_si=on:rtra=on:rawr=on:to=lpo:sos=all:urr=ec_only:nwc=5.0:amm=off:br=off:ss=axioms:sfv=off:i=480:i=348_0");
    quick.push("lrs+10_1:1_anc=all_dependent:sos=all:i=32280:ep=R:i=349_0");
    quick.push("fmb+10_1:1_fde=unused:i=1680:i=869_0");
    quick.push("dis+1011_2:1_slsqr=1,8:to=lpo:plsq=on:fde=none:sp=unary_first:erd=off:slsq=on:s2a=on:i=24000:s2at=5.0:av=off:i=9506_0");
    quick.push("lrs+10_1:1_sos=all:i=10320:sd=2:ep=RS:ss=axioms:i=8835_0");
    quick.push("lrs+11_4:1_bsr=unit_only:sfv=off:to=lpo:irw=on:plsq=on:plsqc=2:sos=all:lma=on:spb=units:plsql=on:fd=preordered:flr=on:cond=on:i=2520:av=off:i=875_0");
    quick.push("dis+1011_39044:804583_si=on:rtra=on:rawr=on:anc=all:bsr=on:to=lpo:plsq=on:plsqr=9,13:uwa=all:nwc=2.0:s2agt=16:thsql=off:updr=off:sac=on:cond=on:avsq=on:s2a=on:avsqr=302,909:i=2040:thsqd=32:awrs=decay:awrsf=20:nm=0:bd=off:thsqc=32:gsp=on:thsq=on:i=1104_0");
    quick.push("lrs+1010_1:3_anc=all_dependent:bsr=on:sos=on:nwc=1.5:i=600:aac=none:fsr=off:i=375_0");
    quick.push("dis+1002_1:1_slsqr=1,4:slsqc=0:slsq=on:bs=on:i=26280:av=off:slsql=off:i=382_0");
    quick.push("lrs+10_1:128_to=lpo:drc=off:sas=z3:norm_ineq=on:fde=none:sp=reverse_arity:sos=all:gve=force:spb=intro:uwa=one_side_constant:i=720:asg=cautious:ss=axioms:i=384_0");
    quick.push("ott+10_4:1_sp=reverse_arity:sos=all:spb=goal:urr=on:skr=on:cond=fast:st=1.772:sd=6:br=off:ep=RS:ss=axioms:nm=40:i=19200:i=4461_0");
    quick.push("ott+10_1:1_sos=all:urr=on:fd=off:s2pl=no:s2a=on:av=off:sfv=off:i=840:i=387_0");
    quick.push("ott+11_1:1_bsd=on:sos=on:fs=off:spb=goal_then_units:urr=on:nwc=5.0:fsr=off:i=720:i=389_0");
    quick.push("lrs+11_1:1_to=lpo:drc=off:urr=ec_only:br=off:i=480:i=392_0");
    quick.push("lrs+1010_1:1_si=on:rtra=on:rawr=on:sos=on:fd=off:s2a=on:i=720:av=off:bd=off:i=404_0");
    quick.push("dis+1010_7534:911605_bsr=on:to=lpo:sims=off:sos=on:erd=off:abs=on:sac=on:s2a=on:bs=unit_only:s2at=3.4:nm=0:i=7080:i=407_0");
    quick.push("lrs+10_1:1_sos=on:spb=goal_then_units:urr=on:atotf=0.1:nwc=5.0:sac=on:lcm=predicate:s2a=on:s2at=2.0:rnwc=on:i=720:i=429_0");
    quick.push("lrs+10_1:1_to=lpo:sos=on:spb=goal:urr=on:st=3.7:sd=4:ss=axioms:i=1080:i=434_0");
    quick.push("lrs+10_1:1_sos=all:st=3.0:i=58560:sd=10:ss=axioms:i=27084_0");
    quick.push("lrs+10_1:3_to=lpo:sp=reverse_arity:erd=off:drc=off:urr=on:bd=preordered:flr=on:lwlo=on:s2a=on:s2at=3.0:ss=included:i=7200:i=450_0");
    quick.push("dis+1010_1:1_anc=all:sfv=off:etr=on:sp=reverse_arity:erd=off:urr=on:lcm=reverse:uwa=interpreted_only:nwc=3.0:skr=on:flr=on:sac=on:i=10000:bs=on:aac=none:nm=5:gsp=on:i=901_0");
    quick.push("dis+1011_3:29_drc=off:irw=on:fde=unused:spb=goal_then_units:urr=ec_only:bce=on:nwc=2.0:updr=off:i=2880:awrs=decay:awrsf=32:av=off:gsp=on:i=1903_0");
    quick.push("lrs+10_8:1_sfv=off:sos=all:urr=ec_only:fd=off:i=4440:av=off:bd=off:i=3182_0");
    quick.push("lrs+4_1:1_sos=on:flr=on:s2pl=on:s2a=on:s2at=3.0:sd=1:ss=included:i=4680:i=475_0");
    quick.push("dis+11_1:1_to=lpo:urr=ec_only:i=5880:ep=R:av=off:i=3024_0");
    quick.push("lrs+10_1:1024_bsr=unit_only:fde=none:bsd=on:sp=frequency:sos=on:urr=ec_only:nwc=5.0:lcm=reverse:ss=axioms:fsd=on:av=off:gsp=on:i=960:i=509_0");
    quick.push("dis+1011_1:2_bsr=unit_only:erd=off:abs=on:urr=ec_only:bce=on:avsqc=2:newcnf=on:cond=fast:avsq=on:s2a=on:i=3600:ep=RS:i=2054_0");
    quick.push("lrs+10_1:1024_sos=on:urr=on:atotf=0.1:sd=1:ss=included:i=3480:i=535_0");
    quick.push("lrs+10_1:1_gve=force:nwc=5.0:i=40000:ev=cautious:i=539_0");
    quick.push("ins+10_1:1_tgt=full:fde=unused:bsd=on:sp=unary_first:gve=cautious:erd=off:lcm=reverse:rnwc=on:nwc=3.0:igwr=on:igrr=1/8:i=10000:awrs=decay:awrsf=256:ins=1:igs=1011:i=551_0");
    quick.push("ott+1011_1:32_bsr=unit_only:drc=off:br=off:i=1560:av=off:fsr=off:i=1103_0");
    quick.push("dis+1011_1:1_si=on:rtra=on:rawr=on:sos=on:ep=RSTC:av=off:i=1560:i=592_0");
    quick.push("lrs+10_1:1_bsr=on:sos=all:ss=axioms:av=off:i=2160:i=600_0");
    quick.push("lrs+10_8:1_bsr=on:drc=off:sas=z3:sims=off:sp=frequency:sos=on:foolp=on:erd=off:spb=goal_then_units:urr=on:s2agt=8:alpa=random:thsql=off:skr=on:flr=on:updr=off:sac=on:cond=on:s2a=on:i=19440:add=large:thsqd=16:awrs=decay:awrsf=250:bd=off:thsqc=64:thsq=on:i=606_0");
    quick.push("lrs+10_1:1_sos=all:lma=on:cond=on:i=25680:ep=RSTC:ss=axioms:i=7653_0");
    quick.push("ins+10_1:1_igrp=4000:igpr=on:igrpq=1.5:igbrr=1.0:igs=1010:i=52440:i=615_0");
    quick.push("lrs+1011_1:1_i=19080:sd=2:ss=axioms:i=8842_0");
    quick.push("lrs+10_1:1_plsq=on:plsqc=1:plsqr=32,1:urr=on:br=off:i=28080:nm=5:i=7937_0");
    quick.push("dis+10_1:512_tgt=ground:drc=off:sp=unary_first:spb=intro:fd=preordered:s2a=on:i=40000:kws=precedence:ins=2:i=5047_0");
    quick.push("dis+1010_2:3_fs=off:s2agt=32:nwc=5.0:s2a=on:nm=0:fsr=off:i=960:i=703_0");
    quick.push("lrs+10_1:1_sos=on:spb=units:urr=on:sd=1:ss=included:av=off:i=18240:i=3546_0");
    quick.push("lrs+10_1:32_s2agt=10:s2a=on:ss=axioms:sgt=8:i=11760:i=743_0");
    quick.push("lrs+1011_1:128_slsqr=1,8:sp=reverse_arity:sos=on:bd=off:slsq=on:nwc=2.0:slsqc=0:amm=sco:cond=fast:s2a=on:s2at=1.5:nm=0:rnwc=on:afr=on:i=13800:i=1593_0");
    quick.push("lrs+1002_1:28_bsr=unit_only:sos=on:flr=on:i=64080:i=55761_0");
    quick.push("lrs+10_1:2_to=lpo:drc=off:sp=reverse_arity:spb=units:nwc=2.0:lwlo=on:i=1178:bd=off:i=760_0");
    quick.push("dis+1011_1:1_nwc=5.0:i=40000:canc=force:bd=off:ev=cautious:i=789_0");
    quick.push("lrs+1011_1:1_drc=off:fde=none:erd=off:urr=on:atotf=0.2:i=8640:gsp=on:i=3227_0");
    quick.push("lrs+10_1:1_sos=on:ep=RS:ss=included:i=3360:i=815_0");
    quick.push("lrs+10_3:1_sos=on:urr=on:nwc=5.0:s2a=on:s2at=3.0:sd=5:br=off:ss=included:rnwc=on:sgt=16:i=2160:i=1655_0");
    quick.push("dis+10_1:4_slsqr=1,8:bsd=on:sas=z3:abs=on:nwc=3.0:slsqc=2:slsq=on:i=40000:slsql=off:fsd=on:i=1674_0");
    quick.push("lrs+10_1:1024_sos=all:urr=on:br=off:i=5400:nm=4:gsp=on:i=4376_0");
    quick.push("ins+10_1:1_tgt=ground:fde=none:sp=weighted_frequency:gve=cautious:erd=off:lcm=reverse:rnwc=on:uwa=all:nwc=3.0:igwr=on:igrr=1/8:i=10000:awrs=decay:awrsf=250:ins=1:igs=1002:i=1020_0");
    quick.push("lrs+1002_1:1_sos=on:flr=on:ss=axioms:i=6000:i=5600_0");
    quick.push("lrs+10_1:32_tgt=full:drc=off:i=40000:kws=inv_frequency:awrs=converge:i=35176_0");
    quick.push("lrs+21_1:64_bsr=on:sas=z3:fde=none:to=lpo:sims=off:bsd=on:add=large:sp=frequency:sos=on:fs=off:spb=units:urr=ec_only:bd=off:awrs=decay:fd=off:nwc=3.0:flr=on:avsqc=2:avsq=on:st=1.2:avsql=on:sd=3:afp=3:ss=axioms:fsr=off:sffsmt=on:afq=1.717:rnwc=on:afr=on:sgt=16:i=13560:i=1034_0");
    quick.push("dis+11_1:1_si=on:rtra=on:rawr=on:slsqr=1,2:erd=off:urr=on:br=off:nwc=3.0:slsqc=2:slsq=on:s2a=on:i=10000:nm=0:ins=1:av=off:bd=off:i=1046_0");
    quick.push("lrs+32_1:1_slsqr=15,16:sas=z3:sos=all:slsqc=2:flr=on:slsq=on:st=1.5:s2a=on:i=5880:s2at=2.0:sd=4:ep=R:nm=2:gsp=on:ss=axioms:i=2196_0");
    quick.push("dis+1011_1:227_bsr=unit_only:slsqr=307,512:sas=z3:plsq=on:plsqc=1:avsqr=97,32:plsqr=27942579,963352:slsql=off:sp=occurrence:abs=on:drc=off:plsql=on:awrs=converge:fd=preordered:slsq=on:slsqc=1:avsqc=1:amm=off:avsq=on:st=3.0:awrsf=256:ss=axioms:i=14400:i=2284_0");
    quick.push("lrs+1_5:1_spb=units:awrs=decay:sac=on:lcm=predicate:i=4080:i=1271_0");
    quick.push("dis+1011_1:1_to=lpo:spb=goal_then_units:nwc=3.0:sd=1:ss=included:i=10440:i=2708_0");
    quick.push("lrs+1002_1:1_to=lpo:sas=z3:fde=none:sos=all:spb=goal:nwc=3.0:newcnf=on:st=2.0:i=3360:afr=on:ss=axioms:i=1379_0");
    quick.push("dis+10_1:28_urr=on:br=off:nwc=10.0:s2agt=8:cond=on:s2a=on:i=10000:s2at=1.5:bs=unit_only:gsp=on:er=filter:i=1397_0");
    quick.push("lrs+1002_1:1_urr=ec_only:i=31080:sd=1:nm=0:ss=axioms:i=1443_0");
    quick.push("lrs+10_1:1_bsr=unit_only:plsq=on:plsqc=1:sos=all:plsql=on:s2a=on:s2at=1.5:sd=2:ss=axioms:av=off:i=5760:i=4441_0");
    quick.push("lrs+1010_1:1_spb=goal_then_units:nwc=2.0:st=5.0:ss=axioms:i=15360:i=6859_0");
    quick.push("lrs+10_1:1_to=lpo:drc=off:sims=off:sp=frequency:bce=on:fd=preordered:gs=on:newcnf=on:dr=on:i=55680:nm=2:i=6093_0");
    quick.push("lrs+10_1:1_bsr=unit_only:plsq=on:sos=all:atotf=0.1:sd=1:ss=included:i=11640:i=7637_0");
    quick.push("ott+1002_1:1_sos=all:ss=axioms:av=off:gs=on:i=25200:i=16786_0");
    quick.push("lrs+1004_1:734_sp=occurrence:erd=off:urr=on:br=off:gs=on:nwc=3.0:s2agt=16:updr=off:s2a=on:i=31627:awrs=converge:ep=RSTC:awrsf=70:av=off:i=28765_0");
    quick.push("ott+10_75:754_anc=all:slsqr=1,1:fde=unused:to=lpo:add=large:spb=goal_then_units:abs=on:drc=off:atotf=0.3115:fd=preordered:slsq=on:nwc=4.0:slsqc=1:nicw=on:gsem=off:gsaa=from_current:gs=on:i=100560:i=9370_0");
    quick.push("lrs+10_1:1_to=lpo:sos=all:spb=units:sac=on:newcnf=on:aac=none:ss=axioms:nm=2:i=11400:i=5638_0");
    quick.push("ott+10_1:7_bsr=on:sas=z3:afp=1000:ss=axioms:sffsmt=on:sgt=4:i=45240:i=1712_0");
    quick.push("lrs+1010_1:1_bsr=unit_only:to=lpo:sas=z3:nwc=10.0:flr=on:newcnf=on:cond=on:i=7080:i=5287_0");
    quick.push("fmb+10_1:1_i=126480:i=1816_0");
    quick.push("lrs+2_1:128_si=on:rtra=on:rawr=on:drc=off:spb=units:thsqr=4,7:nwc=1.94:lwlo=on:i=287832:thsqd=32:awrs=decay:awrsf=20:fsd=on:nm=2:thsqc=32:thsq=on:i=259803_0");
    quick.push("lrs+1010_1:1_fde=unused:sos=on:newcnf=on:i=23160:nm=2:bd=off:gsp=on:i=11350_0");
    quick.push("lrs+10_1:1_sfv=off:sos=all:urr=on:br=off:fd=off:s2agt=64:s2a=on:i=6960:s2at=2.0:i=4064_0");
    quick.push("dis+10_1:128_tgt=ground:drc=off:sp=const_frequency:i=40000:ins=1:i=35747_0");
    quick.push("dis+10_1:1_fde=unused:urr=on:s2agt=32:slsq=on:s2a=on:i=29760:i=13576_0");
    quick.push("ott+3_1:1_plsq=on:plsqr=7,41:sp=frequency:sos=on:spb=goal_then_units:urr=on:flr=on:sac=on:lcm=predicate:gsp=on:i=5160:i=2085_0");
    quick.push("lrs+1003_1:32_bce=on:nwc=5.0:st=3.2:ss=included:av=off:i=17400:i=2126_0");
    quick.push("dis+10_2:1_si=on:rtra=on:rawr=on:slsqr=1,4:plsq=on:sp=reverse_arity:spb=goal_then_units:lcm=predicate:nwc=3.0:s2agt=47:slsqc=1:slsq=on:s2a=on:i=11880:nm=2:av=off:fsr=off:i=6611_0");
    quick.push("lrs+10_1:1_sos=on:i=21480:sd=1:ss=included:i=9173_0");
    quick.push("dis+1011_1:1_anc=all_dependent:slsqr=5,4:plsq=on:fde=none:plsqr=9,4:acc=on:slsq=on:slsqc=1:ins=1:i=2880:i=2435_0");
    quick.push("dis+1011_1:28_to=lpo:sp=frequency:drc=off:fd=preordered:fsr=off:i=4080:i=2502_0");
    quick.push("ott+1_29:26_to=lpo:sp=frequency:av=off:i=15480:i=2615_0");
    quick.push("dis+1010_1:128_anc=all:slsqr=1,1:irw=on:bsd=on:etr=on:sp=reverse_frequency:sos=on:erd=off:abs=on:slsq=on:slsqc=0:amm=sco:avsq=on:s2a=on:bs=on:i=8280:i=2637_0");
    quick.push("ott+10_8:1_bsr=unit_only:sos=all:urr=on:bce=on:br=off:nwc=3.0:alpa=true:flr=on:bs=on:i=3360:ep=R:ins=1:fsr=off:amm=off:gsp=on:i=2653_0");
    quick.push("lrs+10_1:1_bsr=unit_only:slsqr=211,119:to=lpo:drc=off:avsql=on:sp=reverse_frequency:spb=goal_then_units:rnwc=on:inw=on:nwc=10.0:slsqc=0:slsq=on:st=2.0:avsq=on:i=12360:fsr=off:ss=included:sgt=16:slsql=off:i=2669_0");
    quick.push("lrs+10_1:14_sas=z3:fde=unused:to=lpo:sp=frequency:erd=off:abs=on:urr=on:bce=on:nwc=3.0:sac=on:aac=none:i=8640:i=2846_0");
    quick.push("lrs+1_1:1024_slsqr=1,1:slsqc=0:skr=on:slsq=on:dr=on:s2a=on:s2pl=no:i=34680:s2at=2.7:av=off:gsp=on:i=17373_0");
    quick.push("lrs+10_1:1_urr=on:nwc=10.0:st=1.5:i=87000:ss=included:i=2939_0");
    quick.push("ott+1_1:24_drc=off:fd=preordered:s2a=on:i=5040:i=3020_0");
    quick.push("dis+10_1:1_bsr=on:sas=z3:fde=none:etr=on:sos=on:erd=off:spb=goal_then_units:urr=ec_only:bce=on:atotf=0.11:nwc=2.0:avsqc=1:sac=on:newcnf=on:nicw=on:avsq=on:i=6120:fsd=on:nm=0:amm=off:i=3032_0");
    quick.push("ott+1_2478097:673417_sims=off:urr=on:awrs=decay:st=3.0:lcm=reverse:sd=1:awrsf=32:ss=axioms:av=off:fsr=off:i=7200:i=3061_0");
    quick.push("lrs+10_1:1_plsq=on:to=lpo:sos=all:spb=goal:urr=on:newcnf=on:cond=fast:i=4320:i=3111_0");
    quick.push("ott+10_1:1_st=2.0:i=409560:sd=10:ss=included:i=168459_0");
    quick.push("lrs+10_3:1_to=lpo:sas=z3:sos=all:abs=on:newcnf=on:i=53760:sd=1:ep=RST:nm=2:ss=included:i=50677_0");
    quick.push("dis+11_1:5_slsqr=1,5:tgt=ground:fde=unused:lcm=predicate:gs=on:nwc=5.0:slsqc=1:slsq=on:i=10000:s2at=4.3:thsqd=32:av=off:thsqc=64:thsq=on:i=6336_0");
    quick.push("dis+1010_137062:920759_si=on:rtra=on:rawr=on:anc=none:sfv=off:tgt=ground:fde=unused:bsd=on:sas=z3:gve=cautious:erd=off:spb=goal:abs=on:bce=on:atotf=0.5:uwa=all:gs=on:nwc=3.3:thsql=off:skr=on:avsqc=2:sac=on:newcnf=on:avsq=on:avsqr=383,440:i=8400:aac=none:asg=cautious:amm=sco:thsqc=128:thsq=on:i=6530_0");
    quick.push("dis+10_1:1_urr=on:br=off:s2a=on:i=10800:s2at=3.0:sd=1:ss=included:i=3276_0");
    quick.push("dis+10_1:3_slsqr=1,2:urr=on:br=off:nwc=2.0:s2agt=64:slsqc=1:slsq=on:s2a=on:i=26400:i=9973_0");
    quick.push("lrs+10_1:1_st=3.0:i=4680:sd=5:ss=axioms:i=3417_0");
    quick.push("dis+33_109:91_si=on:rtra=on:rawr=on:slsqr=1,4:drc=off:irw=on:fde=none:foolp=on:spb=units:acc=model:urr=ec_only:bce=on:rnwc=on:gs=on:nwc=10.0:slsqc=1:alpa=false:slsq=on:gsem=on:cond=fast:s2a=on:bs=on:i=25680:s2at=2.0:nm=0:aer=off:afr=on:gsp=on:slsql=off:i=3691_0");
    quick.push("dis+22_1:28_plsq=on:plsqr=3,13:lcm=predicate:nwc=2.0:s2a=on:i=40000:s2at=1.9:nm=4:av=off:bd=off:i=21178_0");
    quick.push("lrs+11_1:64_si=on:rtra=on:rawr=on:plsq=on:fde=none:plsqc=1:to=lpo:etr=on:sp=frequency:erd=off:lma=on:spb=goal:bce=on:plsql=on:awrs=decay:nwc=3.0:flr=on:lwlo=on:bs=on:dr=on:awrsf=8:ins=2:afq=1.0:i=9120:i=8134_0");
    quick.push("lrs+1010_1:1_sos=all:s2a=on:i=53400:s2at=5.0:ep=RST:i=28482_0");
    quick.push("dis+3_1:16_plsq=on:plsqr=319,32:sos=on:spb=goal:lcm=reverse:s2a=on:i=5040:s2at=2.0:nm=2:av=off:i=4421_0");
    quick.push("lrs+10_8:1_sas=z3:fde=unused:sos=all:urr=on:nwc=10.0:br=off:ep=R:ins=1:i=19920:i=4446_0");
    quick.push("ott+1002_1:1_tgt=full:irw=on:plsq=on:fde=unused:plsqc=1:plsqr=19,2:gve=cautious:i=100000:av=off:er=known:i=4502_0");
    quick.push("ott+10_1:1_si=on:rtra=on:rawr=on:slsqr=1,2:urr=on:br=off:slsqc=1:slsq=on:i=23400:fsr=off:gsp=on:i=18385_0");
    quick.push("dis+10_1:1_erd=off:drc=off:urr=on:br=off:ss=axioms:i=7440:i=4657_0");
    quick.push("lrs+1002_2:3_anc=all_dependent:bsr=on:to=lpo:drc=off:sas=z3:fde=unused:sp=frequency:sos=on:abs=on:urr=on:lcm=reverse:rnwc=on:fd=preordered:gs=on:nwc=10.0:skr=on:flr=on:avsqc=1:updr=off:gsem=on:cond=on:avsq=on:bs=unit_only:i=13080:gsaa=full_model:ins=1:fsr=off:amm=off:afr=on:i=4841_0");
    quick.push("dis+1011_2:1_urr=on:fd=preordered:nwc=5.0:avsqc=1:avsq=on:s2a=on:avsqr=65,8:i=12720:fsd=on:fsr=off:ss=included:i=5061_0");
    quick.push("lrs+10_1:1024_to=lpo:tgt=full:drc=off:sp=unary_frequency:i=100000:i=97253_0");
    quick.push("dis+10_1:1_to=lpo:tgt=full:drc=off:fd=preordered:i=100000:i=58991_0");
    quick.push("dis+1002_1:28_bsr=on:slsqr=5,3:irw=on:fde=none:sims=off:slsq=on:slsqc=0:cond=on:s2a=on:s2at=1.5:fsd=on:av=off:gsp=on:i=7920:i=5165_0");
    quick.push("ott+4_1:1_sp=frequency:spb=units:bce=on:atotf=0.5:i=300720:ins=1:i=11466_0");
    quick.push("lrs+1011_1:1_tgt=ground:i=100000:av=off:i=6039_0");
    quick.push("dis+1011_1:1_sfv=off:slsqr=46,31:tgt=ground:thi=overlap:sas=z3:sp=const_frequency:abs=on:thsqr=7,4:tha=some:slsqc=2:flr=on:slsq=on:thitd=on:i=40000:s2at=3.0:thsqd=32:nm=0:bd=off:thsqc=32:thsq=on:i=6284_0");
    quick.push("lrs+10_1:1_si=on:rtra=on:rawr=on:sos=on:urr=on:rnwc=on:nwc=5.0:i=75600:i=59699_0");
    quick.push("lrs+0_1:1_slsqr=1,1:sas=z3:sos=on:slsq=on:slsqc=0:newcnf=on:st=4.0:sd=1:ep=R:ss=axioms:i=45600:i=6903_0");
    quick.push("dis+10_1:1_flr=on:st=1.4:i=60120:ss=included:i=27845_0");
    quick.push("dis+1002_1:1_to=lpo:tgt=ground:sas=z3:abs=on:tha=some:sac=on:nicw=on:i=40000:aac=none:i=7486_0");
    quick.push("lrs+1011_1:6_tgt=ground:bce=on:nwc=2.0:updr=off:i=40000:ins=1:av=off:thsqc=32:thsq=on:i=15906_0");
    quick.push("ott+10_1:10_to=lpo:drc=off:fde=unused:foolp=on:spb=units:urr=ec_only:fd=preordered:nwc=3.0:bs=on:i=93360:i=44074_0");
    quick.push("lrs+1010_1:1_tgt=ground:sas=z3:tha=off:nwc=3.0:i=40000:i=8186_0");
    quick.push("lrs+1002_1:18_tgt=ground:thi=strong:fde=none:sims=off:bsd=on:sas=z3:sp=reverse_arity:gve=cautious:spb=goal:abs=on:bce=on:thigen=on:rnwc=on:uwa=all:tha=off:fd=preordered:gs=on:nwc=1.2:kmz=on:skr=on:flr=on:gsem=off:cond=fast:s2a=on:i=40000:add=off:gsaa=from_current:kws=precedence:canc=force:nm=0:amm=off:afr=on:i=25760_0");
    quick.push("lrs+1002_3:2_bsr=on:plsq=on:plsqr=11,6:spb=units:bce=on:gs=on:nwc=8.0:gsem=on:i=54480:av=off:i=16763_0");
    quick.push("lrs+10_1:512_bsr=unit_only:slsqr=1,16:tgt=full:drc=off:irw=on:plsq=on:plsqc=2:plsqr=9798671,477100:sp=weighted_frequency:foolp=on:gve=cautious:erd=off:spb=intro:urr=on:lcm=reverse:plsql=on:uwa=ground:br=off:nwc=5.0:slsqc=1:kmz=on:updr=off:newcnf=on:slsq=on:i=17850:kws=arity_squared:awrs=converge:awrsf=8:av=off:bd=preordered:fsd=on:i=8421_0");
    quick.push("dis+1004_1:1024_sos=all:newcnf=on:i=21240:av=off:gsp=on:i=8664_0");
    quick.push("lrs+10_1:128_to=lpo:drc=off:sp=reverse_frequency:i=26040:awrs=converge:bd=preordered:i=8852_0");
    quick.push("lrs+1011_4:1_anc=all:sas=z3:abs=on:urr=on:br=off:slsq=on:s2a=on:i=40000:afp=20:canc=force:bd=off:amm=off:i=9548_0");
    quick.push("lrs+10_1:64_to=lpo:tgt=ground:drc=off:spb=goal:s2a=on:i=40000:bd=preordered:i=29486_0");
    quick.push("ott+10_8:1_fde=unused:sos=all:spb=intro:urr=on:br=off:flr=on:slsq=on:i=14160:nm=0:slsql=off:i=9876_0");
    quick.push("lrs+10_1:1_sos=on:urr=on:i=61680:ss=axioms:sgt=16:i=10235_0");
    quick.push("lrs+10_1:1_i=24120:sd=1:ss=axioms:i=10364_0");
    quick.push("lrs+2_3:1_bsr=on:to=lpo:drc=off:irw=on:plsq=on:fde=none:plsqc=2:plsqr=1,32:etr=on:sp=frequency:plsql=on:nwc=3.0:s2agt=60:updr=off:lwlo=on:s2a=on:bs=on:i=187080:awrs=decay:awrsf=64:ins=1:nm=20:av=off:fsr=off:bd=preordered:i=44600_0");
    quick.push("lrs+0_1:1_bsr=on:foolp=on:uwa=one_side_interpreted:lwlo=on:cond=fast:bs=on:i=54600:nm=2:av=off:thsqc=64:gsp=on:thsq=on:i=11947_0");
    quick.push("lrs+1002_1:1_sas=z3:urr=on:atotf=0.1:br=off:nwc=3.0:avsqc=2:sac=on:lwlo=on:nicw=on:cond=fast:avsq=on:avsqr=1,16:i=14760:i=12334_0");
    quick.push("lrs+10_1:1_newcnf=on:sd=2:ep=R:ss=axioms:i=62400:i=24791_0");
    quick.push("lrs+10_1:1_bsr=on:sos=all:lma=on:i=72960:aac=none:ep=R:fsr=off:i=13260_0");
    quick.push("dis+1011_2476:889051_anc=none:irw=on:plsq=on:plsqc=1:sims=off:plsqr=3,2:spb=goal:acc=on:urr=ec_only:plsql=on:alpa=true:s2a=on:i=56880:s2at=2.7:awrs=decay:awrsf=1:afr=on:si=on:rtra=on:rawr=on:i=13896_0");
    quick.push("dis+10_1:1_fde=none:bsd=on:s2agt=32:s2a=on:i=38100:fsd=on:i=28569_0");
    quick.push("lrs+10_1:4_drc=off:sp=reverse_frequency:urr=ec_only:lwlo=on:i=70680:awrs=converge:i=30772_0");
    quick.push("ott+11_397:95149_si=on:rtra=on:rawr=on:urr=on:s2a=on:i=150600:awrs=decay:awrsf=30:i=138014_0");
    quick.push("lrs+10_1:1_sos=all:st=1.5:i=58320:ss=axioms:i=33639_0");
    quick.push("dis+21_1:1_to=lpo:fde=none:sp=const_frequency:abs=on:urr=ec_only:nwc=5.0:s2a=on:i=40000:s2at=4.0:aac=none:fsr=off:er=known:i=33805_0");
    quick.push("ott+11_627097:917038_etr=on:foolp=on:spb=units:nwc=5.0:s2agt=7:skr=on:flr=on:s2a=on:i=86520:s2at=1.5:awrs=decay:awrsf=8:nm=6:av=off:i=17470_0");
    quick.push("ott+10_1:1_si=on:rtra=on:rawr=on:tgt=full:fde=unused:fs=off:urr=on:nwc=5.0:s2agt=64:slsqc=1:slsq=on:i=62850:ins=1:fsr=off:i=37088_0");
    quick.push("dis+11_1:64_to=lpo:tgt=full:sp=unary_first:fd=off:nwc=2.0:i=40000:av=off:er=known:i=37580_0");
    quick.push("ott+1_27:428_bsr=unit_only:slsqr=1,4:drc=off:sp=reverse_frequency:uwa=one_side_constant:fd=preordered:nwc=1.5:slsqc=2:skr=on:newcnf=on:slsq=on:i=73320:awrs=converge:awrsf=8:av=off:slsql=off:i=19117_0");
    quick.push("ott+10_1527:478415_si=on:rtra=on:rawr=on:to=lpo:drc=off:foolp=on:i=104880:awrs=decay:awrsf=4:i=19387_0");
    quick.push("lrs+10_1:1024_urr=on:br=off:i=55800:ep=RSTC:i=41200_0");
    quick.push("lrs+1004_4:1_sims=off:sos=all:bd=off:skr=on:st=2.0:sd=1:ss=axioms:i=44880:i=20917_0");
    quick.push("dis+10_1:14_tgt=ground:sp=unary_first:i=40000:awrs=converge:i=21106_0");
    quick.push("lrs+10_1:128_plsq=on:plsqc=2:urr=on:st=1.5:s2a=on:i=63600:ss=axioms:i=21676_0");
    quick.push("lrs+10_1:128_si=on:rtra=on:rawr=on:sos=all:urr=on:br=off:i=80520:i=22877_0");
    quick.push("lrs+10_1:6_tgt=full:drc=off:i=40000:bd=off:i=24111_0");
    quick.push("lrs+10_1:14_to=lpo:drc=off:nwc=10.0:i=143160:i=24176_0");
    quick.push("lrs+10_1:1_acc=on:st=3.0:avsq=on:i=392040:sd=2:ss=axioms:i=24179_0");
    quick.push("lrs+1011_1:5_bsr=on:slsqr=31,16:plsq=on:sims=off:plsqr=4437,256:sp=frequency:sos=all:drc=off:bce=on:awrs=decay:slsq=on:slsqc=0:skr=on:flr=on:updr=off:newcnf=on:lwlo=on:s2pl=no:s2a=on:s2at=4.0:awrsf=97:ins=3:nm=0:av=off:gs=on:i=78000:i=24465_0");
    quick.push("dis+1010_1:1_newcnf=on:i=156360:av=off:i=24736_0");
    quick.push("lrs+10_1:1_slsqr=174554,979069:to=lpo:plsq=on:sp=frequency:spb=goal:urr=on:uwa=ground:fd=preordered:slsq=on:s2a=on:bs=unit_only:i=58560:ins=1:slsql=off:i=27934_0");
    quick.push("dis+1002_3759:419369_si=on:rtra=on:rawr=on:anc=all:sfv=off:to=lpo:etr=on:sp=const_min:erd=off:spb=goal:urr=on:uwa=all:gs=on:nwc=2.0:flr=on:updr=off:sac=on:i=40000:awrs=decay:awrsf=2:nm=4:uhcvi=on:gsp=on:i=32740_0");
    quick.push("ott+10_1:128_anc=all_dependent:to=lpo:drc=off:urr=on:uwa=interpreted_only:nwc=5.0:st=5.0:avsq=on:avsqr=117,34:i=229440:afp=10:aac=none:awrs=converge:ins=1:bd=preordered:ss=axioms:i=100463_0");
    quick.push("lrs+1011_1:1_bsr=on:slsqr=1,2:drc=off:sas=z3:fde=none:etr=on:sp=reverse_frequency:sos=on:spb=units:abs=on:lcm=reverse:fd=preordered:nwc=5.0:slsqc=0:skr=on:avsqc=2:updr=off:slsq=on:cond=on:avsq=on:s2a=on:bs=on:i=128760:s2at=4.0:sd=3:afp=2:aac=none:fsd=on:nm=0:amm=off:ss=axioms:er=filter:slsql=off:i=36083_0");
    quick.push("lrs+10_1:1_sp=weighted_frequency:sos=all:spb=units:urr=ec_only:bce=on:s2a=on:i=97800:aac=none:afr=on:i=37488_0");
    quick.push("lrs+1010_8:1_sas=z3:fs=off:abs=on:urr=ec_only:i=40000:fsr=off:i=37765_0");
    quick.push("lrs+30_1:64_to=lpo:sp=frequency:flr=on:i=129600:i=79164_0");
    quick.push("ott+10_1:1024_anc=all:to=lpo:drc=off:sos=on:sac=on:bs=unit_only:i=172200:afp=20:bd=preordered:afq=2.0:i=81650_0");
    quick.push("dis+33_1:1_slsqr=1,4:tgt=ground:sp=const_min:slsq=on:i=100000:av=off:bd=off:gsp=on:i=41336_0");
    quick.push("ott+10_1:50_drc=off:plsq=on:plsqr=1,32:spb=goal:i=76200:awrs=converge:awrsf=60:i=43760_0");
    quick.push("lrs+1011_1:92_anc=all:bsr=unit_only:sas=z3:irw=on:to=lpo:sims=off:avsqr=41,14:sp=frequency:erd=off:abs=on:urr=on:bd=preordered:awrs=converge:s2agt=64:fd=preordered:nwc=4.0:avsqc=1:newcnf=on:lwlo=on:nicw=on:amm=sco:avsq=on:lcm=reverse:s2a=on:avsql=on:bs=on:awrsf=170:i=114720:i=44836_0");
    quick.push("lrs+1010_1:1_to=lpo:tgt=full:sas=z3:spb=goal:uwa=all:br=off:tha=some:i=100000:bd=off:i=92051_0");
    quick.push("lrs+1002_1:1_plsq=on:fde=unused:plsqr=32,1:erd=off:plsql=on:fd=preordered:nwc=10.0:thsql=off:lwlo=on:s2a=on:s2pl=on:i=215280:thsqd=16:thsqc=128:tac=axiom:thsq=on:i=48489_0");
    quick.push("ott+10_13:991_si=on:rtra=on:rawr=on:drc=off:sp=const_frequency:spb=goal_then_units:uwa=all:fd=preordered:i=209700:awrs=decay:awrsf=1:bd=preordered:i=52668_0");
    quick.push("lrs+1011_1:8_plsq=on:plsqc=1:plsqr=2133,101:sp=reverse_frequency:spb=units:urr=ec_only:bce=on:gs=on:nwc=2.0:skr=on:updr=off:mep=off:dr=on:cond=on:bs=unit_only:i=161160:ep=RST:nm=10:av=off:gsp=on:i=55324_0");
    quick.push("lrs+10_1:1_si=on:rtra=on:rawr=on:plsq=on:sos=all:flr=on:i=76200:i=61890_0");
    quick.push("ott+10_1:1_bsr=on:urr=on:nwc=3.0:i=94800:av=off:i=70451_0");
    quick.push("lrs+10_1:1_to=lpo:drc=off:sp=frequency:spb=goal_then_units:gs=on:i=91200:i=89291_0");
    quick.push("lrs+10_74417:511564_si=on:rtra=on:rawr=on:drc=off:spb=goal_then_units:lwlo=on:bs=on:i=166680:awrs=decay:awrsf=2:bd=off:i=93254_0");
    quick.push("dis+1002_1:32_si=on:rtra=on:rawr=on:to=lpo:tgt=ground:sas=z3:abs=on:tha=off:sac=on:i=100000:awrs=decay:awrsf=256:canc=force:i=98206_0");
    quick.push("ott+10_1:1_urr=on:br=off:skr=on:i=180360:nm=4:gsp=on:i=103539_0");
    quick.push("lrs+10_1:1024_plsq=on:plsqc=1:plsqr=32,1:s2agt=16:updr=off:s2pl=no:i=148440:av=off:i=105342_0");
    quick.push("dis+11_34:25_slsqr=1,4:irw=on:sp=const_min:spb=intro:urr=ec_only:bce=on:s2agt=30:flr=on:updr=off:slsq=on:cond=on:s2a=on:i=201450:s2at=3.2:kws=precedence:awrs=decay:awrsf=23:av=off:i=111592_0");
    quick.push("lrs+10_1:1_to=lpo:sp=occurrence:nwc=5.0:i=383160:sd=4:ss=included:i=364101_0");
  } else {
    // CNF

    // TODO: compute also some nice CNF schedule
    quick.push("lrs+10_1_i=1000:tgt=full_0");
  }
}

void Schedules::getSnakeTptpSatSchedule(const Shell::Property& property, Schedule& quick) {
  // FNT
  quick.push("fmb+10_1:1_bce=on:fmbsr=1.3:i=13800:i=1_0");
  quick.push("ott+1_1:7_bd=off:i=1800:i=30_0");
  quick.push("fmb+10_1:1_i=120:nm=2:i=117_0");
  quick.push("dis+10_1:1_urr=ec_only:newcnf=on:i=720:ep=RS:fsr=off:amm=off:i=1_0");
  quick.push("ott+10_1:32_tgt=full:newcnf=on:i=40000:fsr=off:bd=off:i=2566_0");
  quick.push("fmb+10_1:1_fde=unused:i=1680:i=1513_0");
  quick.push("ott+30_1:12_slsqr=1,2:gs=on:newcnf=on:slsq=on:lwlo=on:bs=unit_only:i=127080:fsd=on:av=off:i=5_0");
  quick.push("ott+10_1:1_si=on:rtra=on:rawr=on:s2a=on:s2at=2.0:i=34560:i=11265_0");
  quick.push("fmb+10_1:1_fmbas=predicate:i=32550:nm=2:gsp=on:i=5597_0");
  quick.push("ott+3_1:1_lcm=predicate:gsp=on:i=2880:i=140_0");
  quick.push("ott+35_1:128_i=123360:i=266_0");
  quick.push("fmb+10_1:1_si=on:rtra=on:rawr=on:newcnf=on:fmbsr=2.0:i=41550:nm=2:i=31976_0");
  quick.push("ott+10_1:1_st=2.0:i=1320:gsp=on:i=575_0");
  quick.push("dis+21_1:1_to=lpo:fde=none:sp=const_frequency:abs=on:urr=ec_only:nwc=5.0:s2a=on:i=40000:s2at=4.0:aac=none:fsr=off:er=known:i=885_0");
  quick.push("fmb+10_1:1_bce=on:skr=on:dr=on:fmbsr=1.47:i=401700:nm=2:gsp=on:i=367554_0");
  quick.push("ott+3_1:1_anc=none:spb=goal_then_units:abs=on:bs=on:fsr=off:i=7680:i=1392_0");
  quick.push("ott+10_1:12_bsr=unit_only:to=lpo:tgt=full:plsq=on:sas=z3:plsqr=1,32:spb=goal_then_units:abs=on:plsql=on:sac=on:avsq=on:avsqr=5,31:i=40000:bd=off:i=15958_0");
  quick.push("fmb+10_1:1_si=on:rtra=on:rawr=on:skr=on:newcnf=on:fmbsr=2.0:i=52200:nm=2:i=24715_0");
  quick.push("ott+1_27:428_bsr=unit_only:slsqr=1,4:drc=off:sp=reverse_frequency:uwa=one_side_constant:fd=preordered:nwc=1.5:slsqc=2:skr=on:newcnf=on:slsq=on:i=73320:awrs=converge:awrsf=8:av=off:slsql=off:i=27757_0");
  quick.push("fmb+10_1:1_fmbas=function:bce=on:skr=on:fmbsr=2.0:i=100350:nm=4:i=93433_0");
  quick.push("ott+10_1:1_st=2.0:i=409560:sd=10:i=369247_0");
  quick.push("ott+4_1:1_sp=frequency:spb=units:bce=on:atotf=0.5:i=300720:ins=1:i=262588_0");
  quick.push("ott+10_1:1_to=lpo:sp=frequency:i=387000:i=336541_0");
}
