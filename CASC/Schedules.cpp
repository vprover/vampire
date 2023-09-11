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
    quick.push("ins+10_1:32_fd=off:fs=off:fsr=off:igrr=4/7:igwr=on:urr=ec_only:i=500:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:32_fd=off:fs=off:fsr=off:igrr=4/7:igwr=on:urr=ec_only:i=591:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:1_br=off:gs=on:igrr=1/32:igs=34:igwr=on:nm=0:sp=const_min:uhcvi=on:updr=off:urr=ec_only:i=34:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:1_br=off:gs=on:igrr=1/32:igs=34:igwr=on:nm=0:sp=const_min:uhcvi=on:updr=off:urr=ec_only:i=201:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:1_igbrr=1.0:igpr=on:igrp=4000:igrpq=1.5:igs=1010:i=911:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:1_awrs=decay:awrsf=250:erd=off:fde=none:gve=cautious:igrr=1/8:igs=1002:igwr=on:ins=1:lcm=reverse:nwc=3.0:rnwc=on:sp=weighted_frequency:tgt=ground:uwa=all:i=1121:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:1_igbrr=1.0:igpr=on:igrp=4000:igrpq=1.5:igs=1010:i=911:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:1_br=off:gs=on:igrr=1/32:igs=34:igwr=on:nm=0:sp=const_min:uhcvi=on:updr=off:urr=ec_only:i=1530:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:4_igrr=1/16:igs=1002:igwr=on:lcm=predicate:sd=2:sos=on:sp=reverse_arity:ss=axioms:st=1.2:i=4989:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:1_igs=2:igwr=on:lcm=predicate:sd=2:sos=on:sp=const_min:ss=axioms:st=1.2:i=7967:si=on:rawr=on:rtra=on_0");
    quick.push("ins+10_1:4_igrr=1/16:igs=1002:igwr=on:lcm=predicate:sd=2:sos=on:sp=reverse_arity:ss=axioms:st=1.2:i=6993:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:1_bs=on:bsr=unit_only:cond=fast:erd=off:flr=on:igpr=on:igrr=1/32:igs=1011:igwr=on:ins=2:lma=on:newcnf=on:nwc=2.0:rnwc=on:s2a=on:s2at=2.51464:s2pl=no:skr=on:to=lpo:updr=off:i=852:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:1_bce=on:bd=off:fde=unused:fsd=on:igs=3:igwr=on:lcm=predicate:sos=on:i=1276:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:1_bs=on:bsr=unit_only:cond=fast:erd=off:flr=on:igpr=on:igrr=1/32:igs=1011:igwr=on:ins=2:lma=on:newcnf=on:nwc=2.0:rnwc=on:s2a=on:s2at=2.51464:s2pl=no:skr=on:to=lpo:updr=off:i=852:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:1_igbrr=1.0:igpr=on:igrpq=2.0:igs=1:i=48277:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:1_igbrr=1.0:igpr=on:igrpq=2.0:igs=1:i=58884:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:1_awrs=decay:awrsf=30:bsr=unit_only:foolp=on:igrr=8/457:igs=10:igwr=on:nwc=1.5:sp=weighted_frequency:to=lpo:uhcvi=on:i=342722:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:1_awrs=decay:awrsf=30:bsr=unit_only:foolp=on:igrr=8/457:igs=10:igwr=on:nwc=1.5:sp=weighted_frequency:to=lpo:uhcvi=on:i=342722:si=on:rawr=on:rtra=on_0");
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
    quick.push("ins+10_1:1_awrs=decay:awrsf=30:bsr=unit_only:foolp=on:igrr=8/457:igs=10:igwr=on:nwc=1.5:sp=weighted_frequency:to=lpo:uhcvi=on:i=342722:si=on:rawr=on:rtra=on_0");
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
   quick.push("ins+10_1:1_awrs=decay:awrsf=30:bsr=unit_only:foolp=on:igrr=8/457:igs=10:igwr=on:nwc=1.5:sp=weighted_frequency:to=lpo:uhcvi=on:i=68:si=on:rawr=on:rtra=on_0");
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
   quick.push("ins+10_1:1_awrs=decay:awrsf=30:bsr=unit_only:foolp=on:igrr=8/457:igs=10:igwr=on:nwc=1.5:sp=weighted_frequency:to=lpo:uhcvi=on:i=68:si=on:rawr=on:rtra=on_0");
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
   quick.push("ins+10_1:1_awrs=decay:awrsf=30:bsr=unit_only:foolp=on:igrr=8/457:igs=10:igwr=on:nwc=1.5:sp=weighted_frequency:to=lpo:uhcvi=on:i=68:si=on:rawr=on:rtra=on_0");
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
   quick.push("ins+10_1:1_awrs=decay:awrsf=30:bsr=unit_only:foolp=on:igrr=8/457:igs=10:igwr=on:nwc=1.5:sp=weighted_frequency:to=lpo:uhcvi=on:i=68:si=on:rawr=on:rtra=on_0");
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
   quick.push("ins+10_1:16_bce=on:fde=unused:igpr=on:igs=35:igwr=on:sp=const_frequency:tgt=full:to=lpo:i=9902:si=on:rawr=on:rtra=on_0");
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
   quick.push("ins+10_1:16_bce=on:fde=unused:igpr=on:igs=35:igwr=on:sp=const_frequency:tgt=full:to=lpo:i=10147:si=on:rawr=on:rtra=on_0");
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

#if VHOL

void Schedules::getSnakeTptpHolSchedule(const Shell::Property& property, Schedule& quick) {  
  // Sub-schedule for 1200Mi strat cap / 9600Mi overall limit
   quick.push("lrs+1002_1:8_bd=off:fd=off:hud=10:tnu=1:i=183:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_c=on:cnfonf=conj_eager:fd=off:fe=off:kws=frequency:spb=intro:i=4:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_au=on:cbe=off:chr=on:fsr=off:hfsq=on:nm=64:sos=theory:sp=weighted_frequency:i=27:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:inj=on:i=2:si=on:rtra=on_0");
   quick.push("lrs+1002_1:128_aac=none:au=on:cnfonf=lazy_not_gen_be_off:sos=all:i=2:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bd=off:e2e=on:sd=2:sos=on:ss=axioms:i=275:si=on:rtra=on_0");
   quick.push("lrs+1004_1:128_cond=on:e2e=on:sp=weighted_frequency:i=18:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_bet=on:cnfonf=off:fd=off:hud=5:inj=on:i=3:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_cnfonf=lazy_not_be_gen:hud=14:prag=on:sp=weighted_frequency:tnu=1:i=37:si=on:rtra=on_0");
   quick.push("lrs+2_16:1_acc=model:au=on:bd=off:c=on:e2e=on:nm=2:sos=all:i=15:si=on:rtra=on_0");
   quick.push("dis+21_1:1_cbe=off:cnfonf=off:fs=off:fsr=off:hud=1:inj=on:i=3:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_aac=none:au=on:cnfonf=lazy_gen:plsq=on:plsqc=1:plsqr=4203469,65536:i=1041:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_av=off:chr=on:plsq=on:slsq=on:i=7:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_acc=on:amm=sco:cs=on:tgt=full:i=16:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_au=on:cnfonf=off:fd=preordered:fe=off:fsr=off:hud=11:inj=on:kws=precedence:s2pl=no:sp=weighted_frequency:tgt=full:i=3:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_apa=on:au=on:bd=preordered:cnfonf=off:cs=on:ixr=off:sos=on:i=3:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_cnfonf=off:cs=on:hud=3:prag=on:sup=off:i=7:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_add=large:cnfonf=lazy_pi_sigma_gen:fe=off:prag=on:i=3:si=on:rtra=on_0");
   quick.push("dis+1004_1:1_cha=on:cs=on:fe=off:hud=1:i=4:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_anc=all_dependent:au=on:cbe=off:fde=unused:ntd=on:i=18:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_e2e=on:sd=1:sgt=8:ss=axioms:i=710:si=on:rtra=on_0");
   quick.push("lrs+1004_1:1_chr=on:prag=on:i=6:si=on:rtra=on_0");
   quick.push("dis+1002_5:1_au=on:bd=off:e2e=on:fde=none:fs=off:fsr=off:sos=on:i=902:si=on:rtra=on_0");
   quick.push("dis+21_1:8_apa=on:cnfonf=off:fd=off:fsr=off:hud=0:ins=1:kws=inv_frequency:nwc=10.0:ss=axioms:st=5.0:i=21:si=on:rtra=on_0");
   quick.push("dis+10_1:1_cnfonf=lazy_gen:fe=off:i=5:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_cnfonf=lazy_not_gen_be_off:cs=on:fe=off:hud=10:inj=on:ins=3:plsq=on:plsqc=1:sd=10:ss=axioms:tnu=1:i=6:si=on:rtra=on_0");
   quick.push("lrs+1002_1:128_au=on:c=on:fsr=off:piset=equals:i=377:si=on:rtra=on_0");
   quick.push("dis+1010_1:4_atotf=0.2:c=on:cbe=off:cnfonf=lazy_simp:fe=off:ins=2:ntd=on:s2a=on:s2at=5.0:sgt=5:ss=axioms:st=1.5:i=779:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_cnfonf=lazy_not_be_gen:ntd=on:sp=const_min:ss=axioms:sup=off:i=19:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:s2a=on:sd=1:sgt=50:ss=axioms:i=879:si=on:rtra=on_0");
   quick.push("dis+1002_1:128_acc=on:er=filter:i=17:si=on:rtra=on_0");
   quick.push("ott+21_1:1_apa=on:au=on:cnfonf=off:sos=on:i=3:si=on:rtra=on_0");
   quick.push("lrs+1010_1:8_cnfonf=off:hud=1:inj=on:tnu=5:i=30:si=on:rtra=on_0");
   quick.push("dis+10_1:1_ixr=off:plsq=on:plsqc=1:plsqr=32,1:s2a=on:i=127:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:cbe=off:cnfonf=conj_eager:cond=on:hi=on:i=100:si=on:rtra=on_0");
   quick.push("dis+10_1:1_anc=none:cnfonf=lazy_gen:fd=preordered:fe=off:hud=10:ins=3:ixr=off:nwc=5.0:plsq=on:plsqc=1:plsqr=32,1:sp=const_frequency:uhcvi=on:i=3:si=on:rtra=on_0");
   quick.push("lrs+10_8:1_au=on:avsq=on:e2e=on:ins=3:s2a=on:s2at=3.0:ss=axioms:i=20:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_cbe=off:hud=5:nm=4:plsq=on:plsqr=7,1:prag=on:sp=const_max:tnu=1:i=86:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cbe=off:nm=2:ntd=on:sd=2:ss=axioms:st=5.0:i=107:si=on:rtra=on_0");
   quick.push("lrs+2_1:1024_cnfonf=lazy_gen:fe=off:hud=15:plsq=on:plsqc=1:plsqr=32,1:i=39:si=on:rtra=on_0");
   quick.push("dis+10_1:1_cnfonf=lazy_not_gen:fsr=off:kws=precedence:nwc=5.0:s2a=on:ss=axioms:st=1.5:i=448:si=on:rtra=on_0");
   quick.push("lrs+10_1:512_au=on:fde=unused:lma=on:nm=32:plsq=on:plsqc=1:plsqr=16121663,131072:sfv=off:sp=const_max:ss=axioms:st=3.0:tgt=full:i=46:si=on:rtra=on_0");
   quick.push("lrs+10_1:10_au=on:av=off:cbe=off:cnfonf=lazy_pi_sigma_gen:ntd=on:plsq=on:plsqc=1:plsqr=32,1:i=98:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_apa=on:au=on:bd=off:cnfonf=off:fd=off:sos=on:sp=weighted_frequency:i=507:si=on:rtra=on_0");
   quick.push("dis+1010_2:3_amm=off:fd=preordered:ixr=off:nm=0:pe=on:piset=equals:prag=on:sac=on:tgt=ground:i=149:si=on:rtra=on_0");
   quick.push("lrs+21_1:16_au=on:bd=off:piset=and:i=39:si=on:rtra=on_0");
   quick.push("lrs+1004_1:1_cnfonf=lazy_pi_sigma_gen:fe=off:gs=on:hud=10:prag=on:tnu=1:i=6:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_aac=none:au=on:e2e=on:nm=2:nwc=10.0:sd=1:ss=axioms:st=3.0:i=1087:si=on:rtra=on_0");
   quick.push("dis+10_1:1_aac=none:cs=on:i=47:si=on:rtra=on_0");
   quick.push("lrs+1010_1:128_av=off:cbe=off:cnfonf=lazy_simp:fsr=off:ntd=on:ss=axioms:st=1.5:i=44:si=on:rtra=on_0");
   quick.push("dis+10_1:1_av=off:bd=off:cnfonf=lazy_gen:fe=off:hud=10:plsq=on:plsqc=1:plsqr=32,1:prag=on:tnu=1:i=432:si=on:rtra=on_0");
   quick.push("lrs+10_7:1_cnfonf=lazy_gen:fe=off:nwc=5.0:plsq=on:i=62:si=on:rtra=on_0");
   quick.push("lrs+1010_1:16_add=large:amm=off:anc=all_dependent:chr=on:fd=off:ins=2:sp=const_max:tnu=5:uhcvi=on:i=31:si=on:rtra=on_0");
   quick.push("dis+10_1:128_hud=1:i=96:si=on:rtra=on_0");
   quick.push("lrs+1002_1:4_au=on:cbe=off:cnfonf=lazy_pi_sigma_gen:hud=15:inj=on:nwc=4.0:s2a=on:sac=on:sp=reverse_arity:i=453:si=on:rtra=on_0");
   quick.push("lrs-1004_1:1_au=on:bsd=on:cbe=off:cnfonf=off:fe=axiom:fsd=on:i=71:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_bd=off:fsr=off:ntd=on:s2a=on:ss=axioms:i=83:si=on:rtra=on_0");
   quick.push("lrs+10_1:128_cnfonf=lazy_not_gen_be_off:hud=1:ins=1:i=11:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cbe=off:cnfonf=lazy_not_gen_be_off:fsr=off:spb=non_intro:i=41:si=on:rtra=on_0");
  // Improves by expected 2321.3567788514306 probs costing 9599 Mi
  // Sub-schedule for 1200Mi strat cap / 9600Mi overall limit
   quick.push("lrs+1004_1:1_chr=on:prag=on:i=6:si=on:rtra=on_0");
   quick.push("dis+10_1:1_avsq=on:cnfonf=off:e2e=on:nm=32:i=150:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_au=on:s2a=on:sd=7:ss=axioms:st=1.5:i=343:si=on:rtra=on_0");
   quick.push("ott+1010_1:4_cbe=off:chr=on:hfsq=on:hfsqr=1,16:hud=3:sac=on:sp=unary_frequency:ss=axioms:st=5.0:tnu=2:i=109:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:c=on:e2e=on:fsr=off:sos=all:sp=const_frequency:ss=axioms:i=253:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:cnfonf=off:sd=1:sgt=16:ss=axioms:i=140:si=on:rtra=on_0");
   quick.push("dis+1010_16:1_acc=model:au=on:avsq=on:cond=fast:plsq=on:plsqc=2:plsqr=9267,262144:i=614:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_e2e=on:fde=unused:fe=axiom:prag=on:sd=1:sos=on:ss=axioms:st=2.0:i=202:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_au=on:cs=on:ins=3:kws=inv_frequency:nwc=10.0:ss=axioms:st=3.0:i=339:si=on:rtra=on_0");
   quick.push("dis+10_1:1_anc=none:cnfonf=lazy_gen:fd=preordered:fe=off:hud=10:ins=3:ixr=off:nwc=5.0:plsq=on:plsqc=1:plsqr=32,1:sp=const_frequency:uhcvi=on:i=283:si=on:rtra=on_0");
   quick.push("dis+2_1:1_cha=on:hud=7:nwc=3.0:prag=on:tnu=2:i=134:si=on:rtra=on_0");
   quick.push("dis+1010_1:64_cnfonf=lazy_simp:fd=off:i=298:si=on:rtra=on_0");
   quick.push("lrs+2_1:8_erd=off:plsq=on:plsqr=32,1:sos=on:i=192:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_bd=off:hud=1:nm=0:prag=on:sd=2:sgt=32:sos=all:ss=axioms:i=258:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1024_au=on:cond=fast:ntd=on:piset=and:plsq=on:plsqc=1:plsqr=183491,1048576:sac=on:tgt=ground:i=90:si=on:rtra=on_0");
   quick.push("dis+1004_16:1_avsq=on:avsqr=1,16:cnfonf=lazy_gen:cs=on:fe=off:tgt=ground:tnu=1:i=231:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:s2a=on:sgt=32:slsq=on:slsqc=1:slsql=off:ss=axioms:i=458:si=on:rtra=on_0");
   quick.push("lrs+1010_1:16_add=large:amm=off:anc=all_dependent:chr=on:fd=off:ins=2:sp=const_max:tnu=5:uhcvi=on:i=31:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_cnfonf=lazy_gen:kws=inv_precedence:nwc=10.0:s2a=on:sp=weighted_frequency:ss=axioms:i=297:si=on:rtra=on_0");
   quick.push("dis+2_1:4_amm=off:au=on:cbe=off:cnfonf=lazy_gen:hfaw=0:hfsq=on:hfsql=off:plsq=on:plsqc=1:plsqr=35,4:sac=on:i=987:si=on:rtra=on_0");
   quick.push("lrs+10_1:1024_avsq=on:avsqc=4:avsqr=584411,1048576:bd=off:bet=on:br=off:chr=on:fsd=on:fsdmm=1:hud=10:nm=0:ntd=on:nwc=9.0:piset=or:plsq=on:plsqc=2:plsql=on:plsqr=852219,1048576:rawr=on:sp=const_frequency:spb=units:i=182:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:e2e=on:fde=none:nwc=10.0:s2a=on:s2at=2.0:i=182:si=on:rtra=on_0");
   quick.push("dis+10_1:8_cha=on:cnfonf=lazy_pi_sigma_gen:fe=axiom:hud=5:plsq=on:plsqr=32,1:prag=on:sos=all:i=154:si=on:rtra=on_0");
   quick.push("dis+1003_1:64_atotf=0.4:au=on:fsr=off:hflw=5:hfsq=on:hfsqc=20:hfsql=off:plsq=on:plsqc=1:plsqr=32,1:i=79:si=on:rtra=on_0");
   quick.push("dis+1010_5:2_anc=all_dependent:awrs=converge:bd=off:bet=on:c=on:cha=on:cnfonf=lazy_not_gen_be_off:fe=axiom:hud=5:kws=precedence:piset=and:prag=on:s2a=on:sac=on:slsq=on:slsqc=1:sp=reverse_arity:ss=axioms:st=1.5:i=216:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_fe=off:hud=10:ins=2:sac=on:sp=const_frequency:i=114:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_acc=on:au=on:bd=off:e2e=on:sgt=8:ss=axioms:i=922:si=on:rtra=on_0");
   quick.push("lrs+10_1:128_au=on:bd=off:cnfonf=lazy_not_gen_be_off:nwc=10.0:piset=and:i=182:si=on:rtra=on_0");
   quick.push("ott+1010_1:1024_au=on:av=off:c=on:cnfonf=conj_eager:piset=equals:s2a=on:sp=occurrence:spb=units:ss=axioms:i=164:si=on:rtra=on_0");
   quick.push("lrs+1004_1:1_cnfonf=lazy_pi_sigma_gen:fe=off:gs=on:hud=10:prag=on:tnu=1:i=50:si=on:rtra=on_0");
   quick.push("dis-30_1:1_acc=on:bd=off:fsr=off:plsq=on:plsqr=32,1:i=368:si=on:rtra=on_0");
   quick.push("dis+2_1:1_bd=off:e2e=on:hud=1:nm=3:piset=or:prag=on:s2a=on:sp=const_max:i=1021:si=on:rtra=on_0");
   quick.push("dis+10_1:1_cnfonf=lazy_gen:fe=off:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=267:si=on:rtra=on_0");
   quick.push("dis+21_1:5_au=on:ntd=on:nwc=5.0:s2a=on:ss=axioms:st=5.0:i=204:si=on:rtra=on_0");
   quick.push("dis+2_1:1024_atotf=0.0802881:au=on:bs=unit_only:cnfonf=lazy_not_gen_be_off:fde=none:nwc=10.0:prag=on:i=26:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_bd=preordered:c=on:cbe=off:cnfonf=lazy_not_gen_be_off:hud=10:ixr=off:prag=on:i=53:si=on:rtra=on_0");
  // Improves by expected 72.38832436063082 probs costing 9563 Mi
  // Sub-schedule for 12000Mi strat cap / 96000Mi overall limit
   quick.push("dis+1002_1:1_aac=none:au=on:e2e=on:nm=2:nwc=10.0:sd=1:ss=axioms:st=3.0:i=4436:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_acc=model:avsq=on:ixr=off:prag=on:s2a=on:sac=on:i=1539:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_bd=off:e2e=on:fde=none:kws=inv_precedence:plsq=on:plsqr=32,1:sos=on:i=408:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_aac=none:au=on:cnfonf=lazy_gen:plsq=on:plsqc=1:plsqr=4203469,65536:i=5205:si=on:rtra=on_0");
   quick.push("dis+1010_1:4_au=on:av=off:cbe=off:nwc=10.0:s2a=on:s2at=3.0:sd=2:ss=axioms:st=5.0:i=1913:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_bd=off:cbe=off:piset=equals:sd=1:sgt=20:sos=all:ss=axioms:i=4350:si=on:rtra=on_0");
   quick.push("ott+1010_1:4_cbe=off:chr=on:hfsq=on:hfsqr=1,16:hud=3:sac=on:sp=unary_frequency:ss=axioms:st=5.0:tnu=2:i=68:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:nwc=5.0:s2a=on:s2at=2.0:sac=on:sd=7:ss=axioms:st=2.0:i=358:si=on:rtra=on_0");
   quick.push("lrs+1010_1:16_add=large:amm=off:anc=all_dependent:chr=on:fd=off:ins=2:sp=const_max:tnu=5:uhcvi=on:i=31:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_cnfonf=lazy_simp:sgt=5:sos=on:ss=axioms:i=279:si=on:rtra=on_0");
   quick.push("lrs+10_8:1_au=on:fde=none:slsq=on:i=258:si=on:rtra=on_0");
   quick.push("dis+2_1:1024_atotf=0.0802881:au=on:bs=unit_only:cnfonf=lazy_not_gen_be_off:fde=none:nwc=10.0:prag=on:i=26:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cbe=off:cnfonf=lazy_not_be_gen:ntd=on:pe=on:i=995:si=on:rtra=on_0");
   quick.push("dis+10_1:8_amm=sco:cbe=off:hflw=5:hfsq=on:hfsqc=14:hfsql=off:hfsqr=4,1:hud=5:ile=on:lma=on:nm=2:ntd=on:prag=on:sac=on:sp=frequency:i=373:si=on:rtra=on_0");
   quick.push("lrs+1010_1:128_au=on:cnfonf=lazy_pi_sigma_gen:hflw=4:hfsq=on:hfsqc=20:hfsql=off:i=253:si=on:rtra=on_0");
   quick.push("lrs+1002_1:14_au=on:bd=off:e2e=on:fde=unused:sac=on:sos=on:i=832:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_chr=on:cnfonf=lazy_not_be_gen:gs=on:hud=5:plsq=on:plsqc=1:plsqr=5,1:prag=on:rawr=on:i=668:si=on:rtra=on_0");
   quick.push("dis+10_1:1_anc=none:cnfonf=lazy_gen:fd=preordered:fe=off:hud=10:ins=3:ixr=off:nwc=5.0:plsq=on:plsqc=1:plsqr=32,1:sp=const_frequency:uhcvi=on:i=40:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_cnfonf=lazy_pi_sigma_gen:fd=off:ntd=on:sd=1:sgt=32:sos=on:ss=axioms:i=294:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_avsq=on:fe=off:fsr=off:hud=10:plsq=on:plsqr=32,1:prag=on:i=187:si=on:rtra=on_0");
   quick.push("lrs+1010_2:3_au=on:fsr=off:sd=4:ss=axioms:st=1.5:i=371:si=on:rtra=on_0");
   quick.push("dis+1003_1:1_au=on:bd=preordered:fde=none:ixr=off:nwc=10.0:i=1827:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_av=off:bd=off:cnfonf=lazy_gen:fe=off:hud=10:plsq=on:plsqc=1:plsqr=32,1:tnu=1:i=70:si=on:rtra=on_0");
   quick.push("lrs+10_1:20_bd=off:cnfonf=lazy_not_be_gen:fe=axiom:hud=10:ins=1:nm=20:prag=on:sos=on:i=316:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_cnfonf=lazy_gen:fe=off:plsq=on:plsqc=1:plsqr=3548551,65536:s2a=on:i=932:si=on:rtra=on_0");
   quick.push("lrs+1010_1:128_au=on:bd=preordered:cnfonf=lazy_pi_sigma_gen:plsq=on:plsqc=1:plsqr=32,1:sos=all:sp=occurrence:i=4714:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:e2e=on:fde=none:nwc=10.0:s2a=on:s2at=2.0:i=8250:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_apa=on:cnfonf=off:fd=off:flr=on:hud=1:lcm=reverse:prag=on:sd=1:sos=on:ss=axioms:i=770:si=on:rtra=on_0");
   quick.push("ott+1010_5:1_av=off:fe=off:ins=1:kws=precedence:sp=reverse_arity:i=794:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_au=on:avsq=on:avsqr=1,16:cond=on:sp=frequency:i=464:si=on:rtra=on_0");
   quick.push("ott+21_1:3_avsq=on:bd=off:cnfonf=lazy_gen:fe=off:hud=10:ixr=off:plsq=on:plsqc=1:plsqr=32,1:prag=on:tnu=1:i=1376:si=on:rtra=on_0");
   quick.push("dis+10_1:1_etr=on:plsq=on:plsqc=1:plsqr=32,1:i=906:si=on:rtra=on_0");
   quick.push("lrs+1002_1:16_bd=off:e2e=on:fde=unused:kws=precedence:sac=on:sos=on:ss=axioms:i=434:si=on:rtra=on_0");
   quick.push("lrs+10_5:4_cnfonf=conj_eager:fe=axiom:hflw=5:hfsq=on:hfsqc=10:hfsql=off:hud=10:plsq=on:sgt=5:spb=goal_then_units:ss=axioms:i=865:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_cnfonf=lazy_simp:hud=5:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=593:si=on:rtra=on_0");
   quick.push("dis+10_1:1_sd=2:sgt=20:slsq=on:ss=axioms:st=6.0:i=443:si=on:rtra=on_0");
   quick.push("dis+10_1:1_atotf=0.1:cbe=off:sd=3:ss=axioms:st=2.0:i=594:si=on:rtra=on_0");
   quick.push("ott+10_1:1024_anc=none:bd=off:e2e=on:fde=none:fsr=off:hud=10:ixr=off:nm=4:nwc=5.0:spb=goal:i=327:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bd=off:e2e=on:sd=2:sos=on:ss=axioms:i=5411:si=on:rtra=on_0");
   quick.push("lrs+10_1:20_au=on:c=on:cbe=off:cnfonf=lazy_gen:ins=1:plsq=on:plsqc=1:plsqr=46,31:sac=on:i=1762:si=on:rtra=on_0");
   quick.push("dis+1003_1:64_cha=on:cnfonf=lazy_gen:hud=9:nwc=8.0:prag=on:i=96:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_hud=5:kws=inv_frequency:nm=16:nwc=2.0:prag=on:sos=on:ss=axioms:i=503:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1024_au=on:cond=fast:ntd=on:piset=and:plsq=on:plsqc=1:plsqr=183491,1048576:sac=on:tgt=ground:i=90:si=on:rtra=on_0");
   quick.push("lrs+10_1:64_hud=5:plsq=on:plsqr=2011171,524288:i=593:si=on:rtra=on_0");
   quick.push("dis-1002_1:1_alpa=false:apa=on:au=on:bd=off:cnfonf=off:e2e=on:er=filter:fde=unused:plsq=on:plsqr=9699663,1048576:s2a=on:sos=on:sp=unary_first:i=1512:si=on:rtra=on_0");
   quick.push("lrs+1002_1:128_cbe=off:cnfonf=lazy_not_gen_be_off:ins=1:i=569:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_bd=off:cnfonf=off:e2e=on:fd=off:fe=axiom:hud=5:prag=on:sos=on:i=501:si=on:rtra=on_0");
   quick.push("lrs+1010_1:3_cnfonf=conj_eager:fsr=off:prag=on:sd=4:sgt=10:ss=axioms:i=562:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:cnfonf=off:fde=unused:kws=precedence:tgt=full:i=406:si=on:rtra=on_0");
   quick.push("dis+1004_1:128_au=on:cbe=off:e2e=on:sac=on:i=582:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_au=on:bd=off:bsr=unit_only:sd=2:sgt=32:sos=all:ss=axioms:i=456:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cbe=off:cnfonf=conj_eager:tgt=ground:i=393:si=on:rtra=on_0");
   quick.push("lrs+1010_1:6_au=on:cnfonf=conj_eager:nwc=10.0:pe=on:prag=on:s2a=on:ss=axioms:st=1.5:i=1335:si=on:rtra=on_0");
   quick.push("dis+1010_16:1_acc=model:au=on:avsq=on:cond=fast:plsq=on:plsqc=2:plsqr=9267,262144:i=3373:si=on:rtra=on_0");
   quick.push("dis+10_1:1024_aac=none:au=on:cnfonf=lazy_gen:plsq=on:plsqc=1:plsqr=32,1:spb=goal_then_units:i=474:si=on:rtra=on_0");
   quick.push("lrs+1002_1:16_amm=sco:cnfonf=lazy_pi_sigma_gen:fe=off:nm=60:piset=all_but_not_eq:plsq=on:plsqc=1:plsqr=2,1:rawr=on:sp=occurrence:ss=included:st=-1.0:i=157:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_amm=off:cs=on:kws=precedence:nwc=10.0:piset=all:s2a=on:sac=on:sp=unary_frequency:spb=goal:ss=axioms:st=3.0:i=590:si=on:rtra=on_0");
   quick.push("dis+10_1:1024_kws=precedence:prag=on:rawr=on:sos=all:sp=unary_first:i=104:si=on:rtra=on_0");
   quick.push("lrs+1010_1:10_au=on:bd=off:cnfonf=lazy_pi_sigma_gen:sp=occurrence:i=414:si=on:rtra=on_0");
   quick.push("dis+10_1:1_av=off:bsd=on:bsr=unit_only:fd=off:hud=8:nm=16:prag=on:i=715:si=on:rtra=on_0");
   quick.push("dis+21_1:5_au=on:ntd=on:nwc=5.0:s2a=on:ss=axioms:st=5.0:i=961:si=on:rtra=on_0");
   quick.push("lrs-1002_1:128_abs=on:bd=preordered:cbe=off:e2e=on:fde=unused:fe=off:tgt=full:i=1213:si=on:rtra=on_0");
   quick.push("lrs+1002_1:12_bd=off:hud=1:ntd=on:piset=equals:prag=on:i=1979:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_amm=off:au=on:bsd=on:cbe=off:cnfonf=lazy_gen:sp=unary_frequency:i=481:si=on:rtra=on_0");
   quick.push("dis+10_8:1_apa=on:cnfonf=off:e2e=on:plsq=on:plsqc=1:plsqr=32,1:ss=axioms:i=783:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_avsq=on:avsqr=1,16:kws=inv_arity:nwc=5.0:sd=1:ss=axioms:i=432:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_atotf=0.5:au=on:cbe=off:cnfonf=lazy_not_be_gen:fe=off:nwc=5.0:spb=units:i=1670:si=on:rtra=on_0");
   quick.push("dis+2_1:1_au=on:hfaw=0:hfsq=on:sp=weighted_frequency:i=90:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:cnfonf=lazy_gen:ixr=off:plsq=on:plsqc=1:plsqr=32,1:i=346:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_cnfonf=lazy_not_gen:hud=10:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=401:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:s2a=on:sd=1:sgt=50:ss=axioms:i=6454:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_avsq=on:fe=off:fsr=off:hud=10:kws=arity:prag=on:i=283:si=on:rtra=on_0");
   quick.push("ott+10_1:1_aac=none:apa=on:au=on:cnfonf=off:ntd=on:nwc=12.0:sos=on:i=865:si=on:rtra=on_0");
   quick.push("lrs+1002_3:4_au=on:av=off:cnfonf=off:fd=off:fsr=off:ins=2:sd=1:sos=on:ss=axioms:i=4528:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_cbe=off:hud=5:nm=4:plsq=on:plsqr=7,1:prag=on:sp=const_max:tnu=1:i=1001:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:cbe=off:cnfonf=conj_eager:cond=on:hi=on:i=102:si=on:rtra=on_0");
   quick.push("ott+1010_3:1_nm=20:s2a=on:s2at=3.0:sp=const_frequency:i=952:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1024_add=large:c=on:cbe=off:cnfonf=lazy_gen:fde=none:nm=30:piset=and:sac=on:uhcvi=on:i=578:si=on:rtra=on_0");
   quick.push("dis+1010_1:4_avsq=on:avsqr=16,1:bet=on:cbe=off:cnfonf=lazy_not_be_gen:hud=5:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=643:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_cnfonf=off:ntd=on:nwc=3.0:s2a=on:sp=const_frequency:i=865:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:erd=off:s2a=on:s2at=3.0:sos=all:i=1174:si=on:rtra=on_0");
   quick.push("ott+1010_1:32_apa=on:atotf=0.3:au=on:c=on:cnfonf=off:fe=off:fsr=off:nm=6:piset=or:sac=on:sos=on:i=644:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_alpa=true:au=on:cs=on:tgt=ground:i=1201:si=on:rtra=on_0");
   quick.push("lrs+1666_1:64_cnfonf=lazy_simp:hud=5:plsq=on:plsql=on:plsqr=152565,524288:tnu=2:i=1046:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_c=on:cnfonf=lazy_simp:fsr=off:hud=5:kws=arity:nm=32:plsq=on:plsqc=1:plsqr=642,29:prag=on:i=222:si=on:rtra=on_0");
  // Improves by expected 228.8984796945416 probs costing 95986 Mi
  // Sub-schedule for 12000Mi strat cap / 96000Mi overall limit
   quick.push("ott+1010_1:4_cbe=off:chr=on:hfsq=on:hfsqr=1,16:hud=3:sac=on:sp=unary_frequency:ss=axioms:st=5.0:tnu=2:i=68:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_chr=on:cnfonf=lazy_not_be_gen:gs=on:hud=5:plsq=on:plsqc=1:plsqr=5,1:prag=on:rawr=on:i=454:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_cnfonf=lazy_simp:hud=5:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=360:si=on:rtra=on_0");
   quick.push("lrs+1002_1:16_amm=sco:cnfonf=lazy_pi_sigma_gen:fe=off:nm=60:piset=all_but_not_eq:plsq=on:plsqc=1:plsqr=2,1:rawr=on:sp=occurrence:ss=included:st=-1.0:i=157:si=on:rtra=on_0");
   quick.push("ott+1004_1:24_anc=none:cbe=off:cnfonf=lazy_not_gen:fe=off:piset=not:prag=on:rp=on:i=5061:si=on:rtra=on_0");
   quick.push("lrs+1002_1:8_av=off:fd=off:hud=5:tnu=1:i=2401:si=on:rtra=on_0");
   quick.push("dis+10_1:1_av=off:e2e=on:nm=4:s2a=on:i=5798:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:cnfonf=lazy_gen:ixr=off:plsq=on:plsqc=1:plsqr=32,1:i=346:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_av=off:bd=off:bet=on:e2e=on:fde=unused:fe=off:plsq=on:prag=on:sos=on:i=1321:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_cnfonf=lazy_gen:kws=inv_precedence:nwc=10.0:i=1312:si=on:rtra=on_0");
   quick.push("ott+2_8:1_add=large:c=on:cnfonf=off:e2e=on:er=filter:hud=5:plsq=on:plsqr=1,1:ss=axioms:i=672:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:c=on:e2e=on:fsr=off:sos=all:sp=const_frequency:ss=axioms:i=1897:si=on:rtra=on_0");
   quick.push("lrs+10_1:40_av=off:fde=unused:ntd=on:plsq=on:plsqc=2:plsqr=411915,1048576:sp=unary_frequency:tgt=full:i=1202:si=on:rtra=on_0");
   quick.push("dis+21_1:1_au=on:cnfonf=lazy_pi_sigma_gen:hfsq=on:hfsqc=40:hfsqr=8,1:ntd=on:sos=on:sp=occurrence:ss=axioms:i=1493:si=on:rtra=on_0");
   quick.push("dis+1010_3:1_av=off:fde=unused:hud=10:nwc=10.0:s2a=on:ss=axioms:i=7679:si=on:rtra=on_0");
   quick.push("lrs+2_1:1024_anc=all:cnfonf=off:cs=on:e2e=on:nm=20:s2at=1.5:slsq=on:slsqr=1,2:spb=goal:i=340:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_acc=model:au=on:nwc=5.0:sd=5:ss=axioms:st=2.5:i=3672:si=on:rtra=on_0");
   quick.push("dis-1002_3:1_acc=model:bd=off:bsd=on:bsdmm=1:cnfonf=lazy_not_be_gen:fd=off:fe=off:ntd=on:nwc=10.0:piset=equals:plsq=on:plsqc=1:plsqr=32,1:sp=const_max:uhcvi=on:i=1535:si=on:rtra=on_0");
   quick.push("dis+10_16:1_hud=1:plsq=on:plsqc=1:plsqr=32,1:prag=on:sd=1:sgt=64:ss=axioms:i=4637:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_fde=unused:prag=on:sd=2:sgt=32:ss=axioms:i=3174:si=on:rtra=on_0");
   quick.push("lrs+1010_1:10_au=on:bd=off:cnfonf=lazy_pi_sigma_gen:sp=occurrence:i=307:si=on:rtra=on_0");
   quick.push("dis+1002_5:1_au=on:bd=off:e2e=on:fde=none:fs=off:fsr=off:sos=on:i=3619:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:cbe=off:fde=none:ins=1:sp=const_max:i=2325:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_au=on:sac=on:sd=5:slsq=on:slsqr=1,4:ss=axioms:st=2.0:i=2341:si=on:rtra=on_0");
   quick.push("lrs+1010_1:16_apa=on:bsd=on:cnfonf=off:hud=10:sac=on:sos=on:ss=axioms:i=7257:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_cnfonf=lazy_gen:fe=off:plsq=on:plsqc=1:plsqr=3548551,65536:s2a=on:i=3710:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_avsq=on:avsqr=1,16:kws=inv_arity:nwc=5.0:sd=1:ss=axioms:i=326:si=on:rtra=on_0");
   quick.push("lrs+1010_1:64_au=on:c=on:e2e=on:flr=on:hfsq=on:hfsql=off:hfsqr=4,1:ins=1:ntd=on:sp=occurrence:i=1100:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:cnfonf=off:fde=unused:kws=precedence:tgt=full:i=406:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_aac=none:bd=preordered:e2e=on:fde=none:fe=axiom:nm=16:nwc=10.0:prag=on:i=1871:si=on:rtra=on_0");
   quick.push("dis+2_1:1_bd=off:e2e=on:hud=1:nm=3:piset=or:prag=on:s2a=on:sp=const_max:i=1194:si=on:rtra=on_0");
   quick.push("dis+10_1:1024_aac=none:au=on:cnfonf=lazy_gen:plsq=on:plsqc=1:plsqr=32,1:spb=goal_then_units:i=474:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_au=on:cnfonf=lazy_gen:ins=3:plsq=on:plsqc=1:plsqr=15142123,262144:sp=reverse_arity:i=3115:si=on:rtra=on_0");
   quick.push("dis+10_1:1024_kws=precedence:prag=on:rawr=on:sos=all:sp=unary_first:i=831:si=on:rtra=on_0");
   quick.push("dis+1666_14:1_cnfonf=lazy_gen:fe=off:hud=10:piset=all_but_not_eq:prag=on:sp=const_max:i=1188:si=on:rtra=on_0");
   quick.push("ott+1010_1:20_cnfonf=lazy_pi_sigma_gen:fe=axiom:plsq=on:plsqc=2:plsqr=32,1:sac=on:sos=all:i=2868:si=on:rtra=on_0");
   quick.push("dis+10_1:4_atotf=0.1:avsq=on:bsr=unit_only:e2e=on:sd=1:sp=const_max:ss=axioms:i=1516:si=on:rtra=on_0");
   quick.push("lrs+1002_1:20_afp=1000:au=on:bsd=on:cnfonf=lazy_not_gen_be_off:sos=all:sp=const_max:i=2321:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_au=on:bd=off:bsd=on:ixr=off:sp=const_max:i=2812:si=on:rtra=on_0");
   quick.push("dis+1002_8:1_bd=off:sd=1:sgt=16:ss=axioms:i=4604:si=on:rtra=on_0");
   quick.push("ott+1002_1:4_c=on:chr=on:cnfonf=lazy_not_be_gen:hud=10:nm=10:piset=all_but_not_eq:rp=on:spb=goal:uhcvi=on:i=2678:si=on:rtra=on_0");
   quick.push("dis+1010_1:4_avsq=on:avsqr=16,1:bet=on:cbe=off:cnfonf=lazy_not_be_gen:hud=5:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=643:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cbe=off:cnfonf=lazy_not_be_gen:ntd=on:pe=on:i=458:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_anc=all_dependent:apa=on:au=on:bd=off:c=on:cnfonf=off:ntd=on:i=2546:si=on:rtra=on_0");
   quick.push("dis+21_1:1_acc=model:au=on:cnfonf=lazy_gen:ins=2:plsq=on:plsqc=1:plsqr=32,1:i=1432:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_cnfonf=lazy_not_gen:hud=10:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=386:si=on:rtra=on_0");
  // Improves by expected 56.1663357045758 probs costing 95861 Mi
  // Sub-schedule for 120000Mi strat cap / 960000Mi overall limit
   quick.push("dis+1002_1:1_cnfonf=lazy_simp:hud=5:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=360:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_au=on:cbe=off:chr=on:fsr=off:hfsq=on:nm=64:sos=theory:sp=weighted_frequency:i=5446:si=on:rtra=on_0");
   quick.push("dis+10_1:1_cnfonf=lazy_gen:fe=off:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=2573:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_av=off:bd=off:cnfonf=lazy_gen:fe=off:hud=10:plsq=on:plsqc=1:plsqr=32,1:tnu=1:i=2655:si=on:rtra=on_0");
   quick.push("dis+1002_16:1_apa=on:au=on:av=off:cnfonf=off:e2e=on:nm=0:nwc=10.0:i=2781:si=on:rtra=on_0");
   quick.push("lrs+1010_1:10_au=on:bd=off:cnfonf=lazy_pi_sigma_gen:sp=occurrence:i=307:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_avsq=on:avsqr=1,16:kws=inv_arity:nwc=5.0:sd=1:ss=axioms:i=1548:si=on:rtra=on_0");
   quick.push("lrs+10_1:3_alpa=true:hud=3:ins=1:ntd=on:plsq=on:plsqc=1:plsqr=32,1:prag=on:s2a=on:s2agt=10:i=5214:si=on:rtra=on_0");
   quick.push("dis+21_1:1_aac=none:bsr=on:nwc=3.0:s2a=on:i=3201:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_chr=on:cnfonf=lazy_not_be_gen:gs=on:hud=5:plsq=on:plsqc=1:plsqr=5,1:prag=on:rawr=on:i=454:si=on:rtra=on_0");
   quick.push("lrs+1002_1:32_au=on:ins=2:nm=16:ntd=on:piset=all_but_not_eq:sp=occurrence:i=3049:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_bd=preordered:cnfonf=off:e2e=on:kws=inv_precedence:lwlo=on:sd=2:ss=axioms:i=7311:si=on:rtra=on_0");
   quick.push("lrs+1002_1:14_au=on:bd=off:e2e=on:fde=unused:sac=on:sos=on:i=6804:si=on:rtra=on_0");
   quick.push("dis+1003_1:1_au=on:bd=preordered:fde=none:ixr=off:nwc=10.0:i=1683:si=on:rtra=on_0");
   quick.push("lrs+10_8:1_au=on:av=off:bd=off:cs=on:e2e=on:hfsq=on:hfsqc=50:hfsql=off:nm=0:i=4688:si=on:rtra=on_0");
   quick.push("dis-1_1:1_amm=off:au=on:cbe=off:spb=intro:i=2207:si=on:rtra=on_0");
   quick.push("dis+1010_1:4_atotf=0.2:c=on:cbe=off:cnfonf=lazy_simp:fe=off:ins=2:ntd=on:s2a=on:s2at=5.0:sgt=5:ss=axioms:st=1.5:i=8216:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_atotf=0.5:au=on:cbe=off:cnfonf=lazy_not_be_gen:fe=off:nwc=5.0:spb=units:i=430:si=on:rtra=on_0");
   quick.push("lrs+1004_1:1_cnfonf=lazy_pi_sigma_gen:fe=off:gs=on:hud=10:prag=on:tnu=1:i=2012:si=on:rtra=on_0");
   quick.push("ott+1010_1:32_apa=on:atotf=0.3:au=on:c=on:cnfonf=off:fe=off:fsr=off:nm=6:piset=or:sac=on:sos=on:i=631:si=on:rtra=on_0");
   quick.push("dis+2_1:1_bd=off:e2e=on:hud=1:nm=3:piset=or:prag=on:s2a=on:sp=const_max:i=8785:si=on:rtra=on_0");
   quick.push("lrs-1002_1:128_abs=on:bd=preordered:cbe=off:e2e=on:fde=unused:fe=off:tgt=full:i=739:si=on:rtra=on_0");
   quick.push("dis+1002_1:1024_fe=off:hud=5:prag=on:i=5473:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bd=off:e2e=on:sd=2:sos=on:ss=axioms:i=43570:si=on:rtra=on_0");
   quick.push("dis+1010_2:3_amm=off:fd=preordered:ixr=off:nm=0:pe=on:piset=equals:prag=on:sac=on:tgt=ground:i=8382:si=on:rtra=on_0");
   quick.push("dis-30_1:1_acc=on:bd=off:fsr=off:plsq=on:plsqr=32,1:i=407:si=on:rtra=on_0");
   quick.push("lrs+10_1:50_cbe=off:cnfonf=lazy_pi_sigma_gen:fe=off:hud=5:plsq=on:plsqr=1,32:sos=all:i=2971:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_aac=none:bd=off:e2e=on:fde=none:fe=off:piset=or:prag=on:rawr=on:sos=on:updr=off:i=9822:si=on:rtra=on_0");
   quick.push("dis+10_5:1_av=off:ntd=on:s2a=on:s2at=3.0:sgt=16:sp=unary_frequency:ss=axioms:i=8425:si=on:rtra=on_0");
   quick.push("lrs+30_1:1_aac=none:au=on:cbe=off:cs=on:nm=2:rawr=on:sos=on:i=3107:si=on:rtra=on_0");
   quick.push("lrs+1002_1:128_aac=none:au=on:cnfonf=lazy_not_gen_be_off:sos=all:i=7967:si=on:rtra=on_0");
   quick.push("lrs+1010_10:959_abs=on:acc=on:bd=off:ccuc=small_ones:cha=on:cnfonf=lazy_simp:fd=preordered:fe=off:hud=3:ile=on:kws=inv_frequency:nm=2:piset=and:sd=5:sp=frequency:spb=goal_then_units:ss=axioms:st=4.5:i=3629:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1024_au=on:fe=axiom:lwlo=on:nm=0:ntd=on:nwc=10.0:spb=non_intro:uhcvi=on:i=939:si=on:rtra=on_0");
   quick.push("dis+1666_14:1_cnfonf=lazy_gen:fe=off:hud=10:piset=all_but_not_eq:prag=on:sp=const_max:i=1188:si=on:rtra=on_0");
   quick.push("dis+21_3:2_avsq=on:cbe=off:e2e=on:flr=on:ile=on:nwc=5.0:piset=or:rawr=on:sp=occurrence:i=3205:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_cnfonf=off:ntd=on:nwc=3.0:s2a=on:sp=const_frequency:i=865:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_au=on:bd=off:cbe=off:cha=on:cnfonf=lazy_pi_sigma_gen:fd=off:fe=off:ntd=on:sp=const_frequency:i=7469:si=on:rtra=on_0");
   quick.push("dis+10_1:10_bd=preordered:e2e=on:fde=none:fe=axiom:hud=3:kws=precedence:nwc=3.0:prag=on:sp=const_max:tgt=full:i=4165:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_au=on:avsq=on:cnfonf=lazy_simp:fsr=off:ntd=on:nwc=10.0:sp=reverse_frequency:ss=axioms:st=1.5:i=13468:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_au=on:bsr=unit_only:cbe=off:fe=off:fsr=off:nm=10:nwc=6.0:plsq=on:plsqc=1:plsqr=32,1:sos=all:i=2635:si=on:rtra=on_0");
   quick.push("dis+1010_1:4_avsq=on:avsqr=16,1:bet=on:cbe=off:cnfonf=lazy_not_be_gen:hud=5:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=631:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_aac=none:au=on:cnfonf=lazy_gen:plsq=on:plsqc=1:plsqr=4203469,65536:i=15557:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_au=on:sac=on:sd=5:slsq=on:slsqr=1,4:ss=axioms:st=2.0:i=2142:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_aac=none:au=on:bd=off:cnfonf=conj_eager:nwc=5.0:sgt=5:sp=reverse_arity:ss=axioms:i=5624:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cbe=off:cnfonf=lazy_not_be_gen:ntd=on:pe=on:i=1665:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_av=off:prag=on:sd=1:sos=on:sp=occurrence:ss=axioms:i=64912:si=on:rtra=on_0");
   quick.push("lrs+10_1:32_atotf=0.1:avsq=on:bsr=on:cnfonf=lazy_gen:fde=unused:i=7801:si=on:rtra=on_0");
   quick.push("ott+2_1:1_au=on:hfsq=on:hfsqc=5:hfsql=off:nwc=5.0:sd=3:ss=axioms:st=5.0:i=15194:si=on:rtra=on_0");
   quick.push("dis-1002_1:1_alpa=false:apa=on:au=on:bd=off:cnfonf=off:e2e=on:er=filter:fde=unused:plsq=on:plsqr=9699663,1048576:s2a=on:sos=on:sp=unary_first:i=6753:si=on:rtra=on_0");
   quick.push("lrs+1002_1:28_bd=off:cnfonf=lazy_simp:plsq=on:plsqr=1,1:prag=on:i=1003:si=on:rtra=on_0");
   quick.push("ott-21_5:4_atotf=0.3:e2e=on:hud=15:ins=1:plsq=on:plsqc=1:plsqr=32,1:sp=unary_frequency:tnu=2:i=13018:si=on:rtra=on_0");
   quick.push("dis+10_1:4_atotf=0.1:avsq=on:bsr=unit_only:e2e=on:sd=1:sp=const_max:ss=axioms:i=1267:si=on:rtra=on_0");
   quick.push("lrs+10_1:20_au=on:c=on:cbe=off:cnfonf=lazy_gen:ins=1:plsq=on:plsqc=1:plsqr=46,31:sac=on:i=2570:si=on:rtra=on_0");
   quick.push("lrs+1004_1:128_cond=on:e2e=on:sp=weighted_frequency:i=13163:si=on:rtra=on_0");
   quick.push("lrs+1666_1:1_au=on:s2a=on:sd=2:ss=axioms:st=5.0:i=5087:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_aac=none:au=on:bd=off:cnfonf=lazy_pi_sigma_gen:s2a=on:sac=on:sd=1:sgt=20:ss=axioms:i=10380:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_bd=off:cbe=off:piset=equals:sd=1:sgt=20:sos=all:ss=axioms:i=4218:si=on:rtra=on_0");
   quick.push("ott+1666_1:1_hfaw=0:hfsq=on:hfsql=off:hfsqr=1,16:hud=15:slsq=on:slsqr=1,2:tnu=2:i=3971:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_anc=all_dependent:au=on:bs=on:sd=5:sp=occurrence:ss=axioms:st=2.0:i=14014:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_ins=1:sgt=8:ss=axioms:i=8517:si=on:rtra=on_0");
   quick.push("dis+10_1:1_av=off:e2e=on:nm=4:s2a=on:i=10148:si=on:rtra=on_0");
   quick.push("lrs+10_1:2_ntd=on:nwc=10.0:plsq=on:plsqc=1:plsqr=2,1:ss=axioms:i=9078:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_bet=on:bsr=on:cnfonf=lazy_pi_sigma_gen:er=filter:kws=inv_frequency:ntd=on:sd=3:ss=axioms:i=16164:si=on:rtra=on_0");
   quick.push("lrs+32_1:1_au=on:bet=on:cbe=off:cs=on:ins=3:i=6102:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:bd=off:e2e=on:fde=unused:nm=4:s2a=on:sos=all:sp=const_frequency:i=10308:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_au=on:avsq=on:bd=off:cbe=off:cnfonf=off:cs=on:hud=5:nm=0:plsq=on:plsqc=1:plsqr=7,1:ss=axioms:tgt=full:i=4041:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_acc=model:au=on:nwc=5.0:sd=5:ss=axioms:st=2.5:i=6901:si=on:rtra=on_0");
   quick.push("lrs-1_1:1_au=on:cbe=off:ntd=on:i=5576:si=on:rtra=on_0");
   quick.push("lrs+1002_1:8_bd=off:fd=off:hud=10:tnu=1:i=2014:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_cnfonf=lazy_gen:fe=off:plsq=on:plsqc=1:plsqr=3548551,65536:s2a=on:i=5115:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_au=on:cnfonf=lazy_pi_sigma_gen:sos=on:ss=axioms:i=13001:si=on:rtra=on_0");
   quick.push("dis+10_1:2_aac=none:acc=on:atotf=0.1:au=on:fde=none:ins=1:ixr=off:nwc=5.0:i=11105:si=on:rtra=on_0");
   quick.push("dis+10_1:1_anc=none:cnfonf=lazy_gen:fd=preordered:fe=off:hud=10:ins=3:ixr=off:nwc=5.0:plsq=on:plsqc=1:plsqr=32,1:sp=const_frequency:uhcvi=on:i=13832:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:s2a=on:sd=1:sgt=50:ss=axioms:i=32887:si=on:rtra=on_0");
   quick.push("dis+1010_2:1_avsq=on:fde=unused:prag=on:i=3362:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_au=on:cnfonf=lazy_simp:nwc=5.0:sgt=5:ss=axioms:st=1.5:i=24965:si=on:rtra=on_0");
   quick.push("lrs+1010_2:1_amm=off:avsq=on:c=on:cbe=off:e2e=on:fsr=off:ins=3:s2a=on:s2at=-1.0:i=15705:si=on:rtra=on_0");
   quick.push("lrs+1010_1:6_au=on:cnfonf=conj_eager:nwc=10.0:pe=on:prag=on:s2a=on:ss=axioms:st=1.5:i=1536:si=on:rtra=on_0");
   quick.push("dis+10_1:1_fde=none:kws=precedence:piset=not:prag=on:slsq=on:slsqc=1:sp=unary_frequency:i=23684:si=on:rtra=on_0");
   quick.push("ott+1004_1:24_anc=none:cbe=off:cnfonf=lazy_not_gen:fe=off:piset=not:prag=on:rp=on:i=4925:si=on:rtra=on_0");
   quick.push("lrs-1010_1:50_au=on:awrs=converge:awrsf=430:bet=on:cbe=off:cha=on:nm=20:sac=on:i=14666:si=on:rtra=on_0");
   quick.push("lrs+1002_1:4_au=on:cbe=off:cnfonf=lazy_pi_sigma_gen:hud=15:inj=on:nwc=4.0:s2a=on:sac=on:sp=reverse_arity:i=3322:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_cnfonf=lazy_gen:kws=inv_precedence:nwc=10.0:i=1810:si=on:rtra=on_0");
   quick.push("dis+1666_1:1_anc=none:bs=on:cbe=off:cha=on:cnfonf=lazy_gen:fe=off:fsr=off:hud=5:kws=precedence:piset=pi_sigma:prag=on:sos=on:sp=frequency:i=2465:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_cbe=off:cnfonf=lazy_pi_sigma_gen:fsr=off:ins=1:kws=inv_precedence:nwc=10.0:ss=axioms:st=2.0:i=41234:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_au=on:cbe=off:cnfonf=lazy_pi_sigma_gen:nm=0:i=14027:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_au=on:cnfonf=conj_eager:nwc=10.0:sac=on:i=27021:si=on:rtra=on_0");
   quick.push("dis-1666_1:1_au=on:cbe=off:cnfonf=lazy_not_be_gen:i=5643:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_apa=on:au=on:cnfonf=off:e2e=on:flr=on:nm=4:s2a=on:i=8612:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:e2e=on:fde=none:nwc=10.0:s2a=on:s2at=2.0:i=3743:si=on:rtra=on_0");
   quick.push("dis+10_1:2_amm=off:bd=preordered:cnfonf=off:e2e=on:fe=off:fsr=off:hud=5:nm=3:s2a=on:sos=on:i=2571:si=on:rtra=on_0");
   quick.push("dis+1010_1:16_cbe=off:cnfonf=conj_eager:fe=off:hud=15:nwc=3.0:piset=pi_sigma:prag=on:sd=5:sp=weighted_frequency:ss=axioms:st=2.0:i=35728:si=on:rtra=on_0");
   quick.push("lrs+1004_1:24_i=5433:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_anc=all_dependent:au=on:avsq=on:cnfonf=lazy_pi_sigma_gen:piset=not:i=27944:si=on:rtra=on_0");
   quick.push("ott+10_1:10_cnfonf=lazy_gen:fde=none:sp=const_frequency:i=15814:si=on:rtra=on_0");
   quick.push("lrs+1002_1:128_atotf=0.1:au=on:cbe=off:ntd=on:sp=const_frequency:i=9867:si=on:rtra=on_0");
   quick.push("dis+10_1:1024_aac=none:au=on:cnfonf=lazy_gen:plsq=on:plsqc=1:plsqr=32,1:spb=goal_then_units:i=5419:si=on:rtra=on_0");
   quick.push("dis+1010_1:28_au=on:cnfonf=off:e2e=on:fde=none:nicw=on:s2a=on:s2at=5.0:tgt=full:i=15386:si=on:rtra=on_0");
   quick.push("lrs+1010_1:128_au=on:bd=preordered:cnfonf=lazy_pi_sigma_gen:plsq=on:plsqc=1:plsqr=32,1:sos=all:sp=occurrence:i=4714:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_bd=off:c=on:fsr=off:ntd=on:prag=on:sd=1:sos=all:ss=axioms:st=5.0:i=42749:si=on:rtra=on_0");
   quick.push("lrs+10_1:156_afp=4000:avsq=on:avsqr=4,1:fe=axiom:ss=axioms:tgt=ground:i=19001:si=on:rtra=on_0");
   quick.push("lrs+1_1:1_au=on:cbe=off:cs=on:nm=4:i=14341:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_cnfonf=off:sd=1:ss=axioms:st=3.0:i=13159:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_e2e=on:fde=unused:fe=axiom:prag=on:sd=1:sos=on:ss=axioms:st=2.0:i=6604:si=on:rtra=on_0");
  // Improves by expected 96.50411951866694 probs costing 957886 Mi
  // Sub-schedule for 120000Mi strat cap / 960000Mi overall limit
   quick.push("dis+1002_1:1_au=on:bsr=unit_only:cbe=off:fe=off:fsr=off:nm=10:nwc=6.0:plsq=on:plsqc=1:plsqr=32,1:sos=all:i=2635:si=on:rtra=on_0");
   quick.push("lrs+1666_1:1_au=on:s2a=on:sd=2:ss=axioms:st=5.0:i=41131:si=on:rtra=on_0");
   quick.push("ott+1666_1:1_hfaw=0:hfsq=on:hfsql=off:hfsqr=1,16:hud=15:slsq=on:slsqr=1,2:tnu=2:i=3971:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_au=on:sac=on:sd=5:slsq=on:slsqr=1,4:ss=axioms:st=2.0:i=2142:si=on:rtra=on_0");
   quick.push("dis-1_1:1_amm=off:au=on:cbe=off:spb=intro:i=1314:si=on:rtra=on_0");
   quick.push("dis+1010_2:1_avsq=on:fde=unused:prag=on:i=3362:si=on:rtra=on_0");
   quick.push("lrs+1002_1:14_au=on:bd=off:e2e=on:fde=unused:sac=on:sos=on:i=5756:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_aac=none:au=on:cnfonf=lazy_gen:plsq=on:plsqc=1:plsqr=4203469,65536:i=2607:si=on:rtra=on_0");
   quick.push("ott+2_1:1_au=on:hfsq=on:hfsqc=5:hfsql=off:nwc=5.0:sd=3:ss=axioms:st=5.0:i=15187:si=on:rtra=on_0");
   quick.push("dis-1666_1:1_au=on:cbe=off:cnfonf=lazy_not_be_gen:i=21027:si=on:rtra=on_0");
   quick.push("lrs+1004_1:128_cond=on:e2e=on:sp=weighted_frequency:i=35698:si=on:rtra=on_0");
   quick.push("lrs-1010_1:50_au=on:awrs=converge:awrsf=430:bet=on:cbe=off:cha=on:nm=20:sac=on:i=14573:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_anc=all_dependent:au=on:bs=on:sd=5:sp=occurrence:ss=axioms:st=2.0:i=14014:si=on:rtra=on_0");
   quick.push("dis+10_1:10_bd=preordered:e2e=on:fde=none:fe=axiom:hud=3:kws=precedence:nwc=3.0:prag=on:sp=const_max:tgt=full:i=4165:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_apa=on:au=on:cnfonf=off:e2e=on:flr=on:nm=4:s2a=on:i=8612:si=on:rtra=on_0");
   quick.push("lrs-1_1:1_au=on:cbe=off:ntd=on:i=5576:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:e2e=on:fde=none:nwc=10.0:s2a=on:s2at=2.0:i=4408:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_av=off:prag=on:sd=1:sos=on:sp=occurrence:ss=axioms:i=13925:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:bd=off:e2e=on:fde=unused:nm=4:s2a=on:sos=all:sp=const_frequency:i=117046:si=on:rtra=on_0");
   quick.push("lrs+1004_1:24_i=5433:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_au=on:cbe=off:cnfonf=lazy_pi_sigma_gen:nm=0:i=8192:si=on:rtra=on_0");
   quick.push("lrs+32_1:1_au=on:bet=on:cbe=off:cs=on:ins=3:i=6102:si=on:rtra=on_0");
   quick.push("lrs+1002_8:1_au=on:cs=on:e2e=on:nm=10:s2a=on:i=35602:si=on:rtra=on_0");
   quick.push("ott+1004_1:24_anc=none:cbe=off:cnfonf=lazy_not_gen:fe=off:piset=not:prag=on:rp=on:i=6101:si=on:rtra=on_0");
   quick.push("dis+1010_3039923:1048576_bsr=unit_only:cbe=off:cha=on:cnfonf=off:e2e=on:fsr=off:hud=1:ixr=off:kws=precedence:lma=on:nm=4:piset=or:s2a=on:sp=frequency:spb=goal_then_units:i=28153:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_cnfonf=off:sd=1:ss=axioms:st=3.0:i=13159:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_bet=on:bsr=on:cnfonf=lazy_pi_sigma_gen:er=filter:kws=inv_frequency:ntd=on:sd=3:ss=axioms:i=12389:si=on:rtra=on_0");
   quick.push("dis+1002_16:1_au=on:nwc=5.0:i=37202:si=on:rtra=on_0");
   quick.push("ott+10_1:10_cnfonf=lazy_gen:fde=none:sp=const_frequency:i=15814:si=on:rtra=on_0");
   quick.push("dis+1010_1:28_add=off:cnfonf=lazy_not_gen:kws=frequency:piset=all:i=8801:si=on:rtra=on_0");
   quick.push("ott-21_5:4_atotf=0.3:e2e=on:hud=15:ins=1:plsq=on:plsqc=1:plsqr=32,1:sp=unary_frequency:tnu=2:i=12360:si=on:rtra=on_0");
   quick.push("lrs+10_1:156_afp=4000:avsq=on:avsqr=4,1:fe=axiom:ss=axioms:tgt=ground:i=19001:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_apa=on:cnfonf=off:fd=off:flr=on:hud=1:lcm=reverse:prag=on:sd=1:sos=on:ss=axioms:i=28134:si=on:rtra=on_0");
   quick.push("dis+10_1:1_fde=none:kws=precedence:piset=not:prag=on:slsq=on:slsqc=1:sp=unary_frequency:i=23684:si=on:rtra=on_0");
   quick.push("ott+10_1:10_avsq=on:bd=off:cnfonf=lazy_gen:sd=2:sgt=16:sos=on:ss=axioms:i=56001:si=on:rtra=on_0");
   quick.push("dis+2_1:1_cbe=off:fe=off:i=13068:si=on:rtra=on_0");
   quick.push("dis+10_3:1_anc=all:avsq=on:c=on:cnfonf=off:e2e=on:fd=off:fde=none:ins=3:nwc=5.0:plsq=on:plsqc=1:plsqr=4964065,131072:prag=on:s2a=on:s2agt=64:i=8801:si=on:rtra=on_0");
   quick.push("dis+1010_1:64_bet=on:cond=fast:e2e=on:fe=off:hud=5:nm=0:ntd=on:nwc=7.0:piset=and:prag=on:rawr=on:sgt=40:ss=included:uhcvi=on:i=42318:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_au=on:avsq=on:bd=off:cbe=off:cnfonf=off:cs=on:hud=5:nm=0:plsq=on:plsqc=1:plsqr=7,1:ss=axioms:tgt=full:i=10924:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_anc=all_dependent:cnfonf=conj_eager:cond=fast:fe=axiom:nm=16:s2a=on:s2at=4.0:sd=2:ss=axioms:st=3.0:i=96745:si=on:rtra=on_0");
   quick.push("lrs-1010_8:1_au=on:c=on:ins=1:i=70437:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_aac=none:bd=off:e2e=on:fde=none:fe=off:piset=or:prag=on:rawr=on:sos=on:updr=off:i=11540:si=on:rtra=on_0");
   quick.push("lrs+1002_1:4_au=on:cbe=off:cnfonf=lazy_pi_sigma_gen:hud=15:inj=on:nwc=4.0:s2a=on:sac=on:sp=reverse_arity:i=32059:si=on:rtra=on_0");
   quick.push("lrs+1002_1:128_atotf=0.1:au=on:cbe=off:ntd=on:sp=const_frequency:i=14041:si=on:rtra=on_0");
   quick.push("dis+10_1:1_fe=axiom:fsr=off:hud=5:nwc=6.0:plsq=on:plsqc=2:plsqr=32,1:s2a=on:s2agt=40:sp=weighted_frequency:i=15424:si=on:rtra=on_0");
  // Improves by expected 15.178891728241835 probs costing 948589 Mi
  // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
   quick.push("ott+1666_1:1_hfaw=0:hfsq=on:hfsql=off:hfsqr=1,16:hud=15:slsq=on:slsqr=1,2:tnu=2:i=3971:si=on:rtra=on_0");
   quick.push("dis-1_1:1_amm=off:au=on:cbe=off:spb=intro:i=2207:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_au=on:bsr=unit_only:cbe=off:fe=off:fsr=off:nm=10:nwc=6.0:plsq=on:plsqc=1:plsqr=32,1:sos=all:i=2635:si=on:rtra=on_0");
   quick.push("dis+1010_2:1_avsq=on:fde=unused:prag=on:i=3362:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_apa=on:au=on:cnfonf=off:e2e=on:flr=on:nm=4:s2a=on:i=8612:si=on:rtra=on_0");
   quick.push("dis+1010_3:1_av=off:fde=unused:hud=10:nwc=10.0:s2a=on:ss=axioms:i=129283:si=on:rtra=on_0");
   quick.push("ott+2_1:1_au=on:hfsq=on:hfsqc=5:hfsql=off:nwc=5.0:sd=3:ss=axioms:st=5.0:i=15187:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_cnfonf=off:sd=1:ss=axioms:st=3.0:i=13159:si=on:rtra=on_0");
   quick.push("lrs-1010_1:50_au=on:awrs=converge:awrsf=430:bet=on:cbe=off:cha=on:nm=20:sac=on:i=14573:si=on:rtra=on_0");
   quick.push("dis+1010_1:28_add=off:cnfonf=lazy_not_gen:kws=frequency:piset=all:i=8801:si=on:rtra=on_0");
   quick.push("dis-1666_1:1_au=on:cbe=off:cnfonf=lazy_not_be_gen:i=50861:si=on:rtra=on_0");
   quick.push("lrs+1666_1:1_au=on:s2a=on:sd=2:ss=axioms:st=5.0:i=120493:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_anc=all_dependent:au=on:bs=on:sd=5:sp=occurrence:ss=axioms:st=2.0:i=77525:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_apa=on:cnfonf=off:fd=off:flr=on:hud=1:lcm=reverse:prag=on:sd=1:sos=on:ss=axioms:i=13432:si=on:rtra=on_0");
   quick.push("lrs+10_1:156_afp=4000:avsq=on:avsqr=4,1:fe=axiom:ss=axioms:tgt=ground:i=19001:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_au=on:cnfonf=lazy_simp:nwc=5.0:sgt=5:ss=axioms:st=1.5:i=17538:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1024_au=on:hud=10:ntd=on:ss=included:i=168763:si=on:rtra=on_0");
   quick.push("lrs+2_16:1_acc=model:au=on:bd=off:c=on:e2e=on:nm=2:sos=all:i=84973:si=on:rtra=on_0");
   quick.push("ott+10_1:10_cnfonf=lazy_gen:fde=none:sp=const_frequency:i=15814:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_ins=2:sd=1:ss=axioms:st=3.0:i=173649:si=on:rtra=on_0");
   quick.push("lrs+1002_8:1_au=on:cs=on:e2e=on:nm=10:s2a=on:i=35602:si=on:rtra=on_0");
   quick.push("dis+1002_16:1_au=on:nwc=5.0:i=37202:si=on:rtra=on_0");
   quick.push("lrs+1002_1:14_au=on:bd=off:e2e=on:fde=unused:sac=on:sos=on:i=16361:si=on:rtra=on_0");
   quick.push("lrs+1010_1:3_au=on:bd=off:c=on:cbe=off:fsr=off:ins=1:ss=axioms:st=1.5:i=15670:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_bd=off:ntd=on:plsq=on:plsqc=1:plsqr=32,1:i=137969:si=on:rtra=on_0");
   quick.push("lrs+1004_1:24_i=198698:si=on:rtra=on_0");
   quick.push("dis+1010_1:64_bet=on:cond=fast:e2e=on:fe=off:hud=5:nm=0:ntd=on:nwc=7.0:piset=and:prag=on:rawr=on:sgt=40:ss=included:uhcvi=on:i=42318:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_av=off:prag=on:sd=1:sos=on:sp=occurrence:ss=axioms:i=33524:si=on:rtra=on_0");
   quick.push("dis+10_3366879:524288_awrs=decay:bd=preordered:cbe=off:e2e=on:kws=arity_squared:nwc=3.0:piset=pi_sigma:sac=on:sd=1:sgt=64:sp=const_max:ss=axioms:tgt=full:i=29485:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_au=on:cbe=off:cnfonf=lazy_pi_sigma_gen:nm=0:i=20308:si=on:rtra=on_0");
   quick.push("lrs-1_1:1_au=on:cbe=off:ntd=on:i=22706:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_anc=all_dependent:au=on:cbe=off:cnfonf=lazy_pi_sigma_gen:fde=none:ins=2:nwc=10.0:piset=or:i=99377:si=on:rtra=on_0");
   quick.push("ott+1010_1:4_cnfonf=lazy_simp:fe=off:hud=5:piset=or:prag=on:i=112304:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_chr=on:ntd=on:i=32514:si=on:rtra=on_0");
   quick.push("lrs+10_1:5_av=off:awrs=converge:awrsf=200:kws=precedence:i=31508:si=on:rtra=on_0");
   quick.push("ott+10_1:1_au=on:av=off:sd=1:ss=axioms:st=2.0:i=29617:si=on:rtra=on_0");
   quick.push("lrs-1010_8:1_au=on:c=on:ins=1:i=70437:si=on:rtra=on_0");
   quick.push("dis+1010_4:1_atotf=0.3:erd=off:sd=2:sgt=8:ss=axioms:i=33157:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_av=off:bd=off:cnfonf=lazy_gen:fe=axiom:hud=10:prag=on:ss=axioms:i=37349:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:s2a=on:s2agt=32:sgt=8:ss=axioms:i=98380:si=on:rtra=on_0");
   quick.push("ott+10_1:10_avsq=on:bd=off:cnfonf=lazy_gen:sd=2:sgt=16:sos=on:ss=axioms:i=56001:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:bd=off:e2e=on:fde=unused:nm=4:s2a=on:sos=all:sp=const_frequency:i=141566:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_e2e=on:plsq=on:i=63430:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_av=off:fe=off:sd=2:slsq=on:slsqr=1,16:ss=axioms:st=5.0:i=82580:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cbe=off:cnfonf=lazy_not_be_gen:ntd=on:pe=on:i=220001:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_cnfonf=off:e2e=on:nm=4:ntd=on:s2a=on:i=97391:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_fe=axiom:nwc=5.0:prag=on:sos=on:ss=axioms:i=73072:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_anc=all_dependent:cnfonf=conj_eager:cond=fast:fe=axiom:nm=16:s2a=on:s2at=4.0:sd=2:ss=axioms:st=3.0:i=96745:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:e2e=on:nm=10:sos=all:sp=reverse_arity:i=88102:si=on:rtra=on_0");
   quick.push("lrs+1010_1:4_cnfonf=lazy_not_be_gen:fe=off:hud=10:i=171919:si=on:rtra=on_0");
  // Improves by expected 14.563032764332931 probs costing 3169082 Mi
  // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
   quick.push("ott+1666_1:1_hfaw=0:hfsq=on:hfsql=off:hfsqr=1,16:hud=15:slsq=on:slsqr=1,2:tnu=2:i=3602:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_cnfonf=off:sd=1:ss=axioms:st=3.0:i=13159:si=on:rtra=on_0");
   quick.push("ott+2_1:1_au=on:hfsq=on:hfsqc=5:hfsql=off:nwc=5.0:sd=3:ss=axioms:st=5.0:i=15187:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_apa=on:cnfonf=off:fd=off:flr=on:hud=1:lcm=reverse:prag=on:sd=1:sos=on:ss=axioms:i=28134:si=on:rtra=on_0");
   quick.push("dis+1010_1:64_bet=on:cond=fast:e2e=on:fe=off:hud=5:nm=0:ntd=on:nwc=7.0:piset=and:prag=on:rawr=on:sgt=40:ss=included:uhcvi=on:i=42318:si=on:rtra=on_0");
   quick.push("dis+1002_16:1_au=on:nwc=5.0:i=37202:si=on:rtra=on_0");
   quick.push("ott+10_1:1_au=on:av=off:sd=1:ss=axioms:st=2.0:i=36665:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_anc=all_dependent:au=on:cbe=off:cnfonf=lazy_pi_sigma_gen:fde=none:ins=2:nwc=10.0:piset=or:i=99377:si=on:rtra=on_0");
   quick.push("dis-1666_1:1_au=on:cbe=off:cnfonf=lazy_not_be_gen:i=50861:si=on:rtra=on_0");
   quick.push("ott+1010_1:4_cnfonf=lazy_simp:fe=off:hud=5:piset=or:prag=on:i=112304:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_fe=axiom:nwc=5.0:prag=on:sos=on:ss=axioms:i=73072:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_e2e=on:plsq=on:i=90575:si=on:rtra=on_0");
   quick.push("lrs+1002_1:14_au=on:bd=off:e2e=on:fde=unused:sac=on:sos=on:i=77965:si=on:rtra=on_0");
   quick.push("lrs-1_1:1_au=on:cbe=off:ntd=on:i=99319:si=on:rtra=on_0");
   quick.push("lrs-1010_8:1_au=on:c=on:ins=1:i=97110:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cbe=off:cnfonf=lazy_not_be_gen:ntd=on:pe=on:i=183300:si=on:rtra=on_0");
   quick.push("lrs+1666_1:1_au=on:s2a=on:sd=2:ss=axioms:st=5.0:i=161771:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:bd=off:e2e=on:fde=unused:nm=4:s2a=on:sos=all:sp=const_frequency:i=171310:si=on:rtra=on_0");
  // Improves by expected 2.3738304642733343 probs costing 1393213 Mi
  // Sub-schedule for 500000Mi strat cap / 4000000Mi overall limit
   quick.push("lrs+10_1:1_cnfonf=off:sd=1:ss=axioms:st=3.0:i=13159:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_apa=on:cnfonf=off:fd=off:flr=on:hud=1:lcm=reverse:prag=on:sd=1:sos=on:ss=axioms:i=28134:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_fe=axiom:nwc=5.0:prag=on:sos=on:ss=axioms:i=73072:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_anc=all_dependent:au=on:cbe=off:cnfonf=lazy_pi_sigma_gen:fde=none:ins=2:nwc=10.0:piset=or:i=99377:si=on:rtra=on_0");
   quick.push("ott+1010_1:4_cnfonf=lazy_simp:fe=off:hud=5:piset=or:prag=on:i=112304:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cbe=off:cnfonf=lazy_not_be_gen:ntd=on:pe=on:i=220001:si=on:rtra=on_0");
  // Improves by expected 0.7448542041792773 probs costing 546041 Mi
  // Sun16Jul HOL3: Overall score 2808.1746472908735 probs on average / budget 7225820 Mi

  // Tue: HOL3 2 Overall score 2800.260571768602 probs on average / budget 7372043 Mi
  // Tue: HOL3 Overall score 2798.5308839897193 probs on average / budget 7843409 Mi
  // Sun: HOL3 Overall score 2791.350517910691 probs on average / budget 8511622 Mi
  // Fri: Overall score 2775.567019728554 probs on average / budget 8273879 Mi
  // Tue: Overall score 2758.4199055140407 probs on average / budget 8640381 Mi
}

void Schedules::getSnakeSlhSchedule(const Shell::Property& property, Schedule& quick) {
  if (property.higherOrder()) {
    if (property.hasPolymorphicSym()) {
  // th1_sledgehammering/TH1.txt - but done in a weighted way (problems already covered by the other subscheds weigh less)
  // Sub-schedule for 10000Mi strat cap / 10000Mi overall limit
   quick.push("lrs+10_1:128_au=on:bd=off:cnfonf=off:plsq=on:plsqr=32,1:sac=on:sos=all:i=1086:si=on:rtra=on_0");
   quick.push("ott+1002_1:8_au=on:bd=off:cbe=off:e2e=on:fd=off:inj=on:nicw=on:sd=2:sos=on:sp=reverse_arity:ss=axioms:st=2.0:i=817:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_au=on:e2e=on:er=filter:hud=10:kws=precedence:sos=on:sp=weighted_frequency:ss=axioms:st=3.0:uhcvi=on:i=795:si=on:rtra=on_0");
   quick.push("lrs+21_1:128_av=off:e2e=on:hud=1:prag=on:sd=2:sgt=10:sos=all:ss=axioms:i=494:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bd=off:e2e=on:sd=1:sos=on:sp=frequency:ss=axioms:i=851:si=on:rtra=on_0");
   quick.push("lrs+1002_3:2_au=on:bsr=unit_only:hud=10:ntd=on:piset=all_but_not_eq:s2a=on:s2at=7.0:sd=2:sos=all:ss=axioms:i=970:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_bd=off:cnfonf=lazy_not_gen_be_off:ntd=on:prag=on:s2a=on:s2agt=32:s2at=5.0:sp=unary_frequency:tnu=5:i=11:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_av=off:prag=on:sd=1:sos=on:sp=const_frequency:ss=axioms:i=240:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_bd=off:fde=none:fe=off:kws=precedence:prag=on:sos=on:sp=frequency:i=646:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:fd=off:sd=1:sgt=16:sos=all:ss=axioms:i=583:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_au=on:cnfonf=off:e2e=on:s2a=on:s2agt=16:slsq=on:i=1662:si=on:rtra=on_0");
   quick.push("lrs+1002_1:7_au=on:cnfonf=off:fe=axiom:ins=2:lecc=0.5:nm=32:sd=1:sgt=64:ss=axioms:i=208:si=on:rtra=on_0");
   quick.push("dis+10_1:1_acc=on:apa=on:au=on:avsq=on:avsqr=561497,524288:cnfonf=off:e2e=on:s2a=on:s2agt=64:s2at=2.0:ss=axioms:i=1077:si=on:rtra=on_0");
   quick.push("dis+3_10:23_bd=off:fde=none:fe=off:nwc=5.0:sac=on:sfv=off:sp=occurrence:i=2:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_acc=model:avsq=on:fe=axiom:fsr=off:nm=16:piset=pi_sigma:prag=on:sd=2:sgt=16:sp=weighted_frequency:ss=axioms:i=570:si=on:rtra=on_0");
  // Improves by expected 539.2390664018176 probs costing 9997 Mi
  // Sub-schedule for 20000Mi strat cap / 20000Mi overall limit
   quick.push("lrs+2_3:1_bd=off:fd=off:fde=none:fe=off:prag=on:sos=on:i=567:si=on:rtra=on_0");
   quick.push("dis+1002_1:32_au=on:av=off:cnfonf=off:fsr=off:sd=2:sgt=4:sos=on:ss=axioms:i=315:si=on:rtra=on_0");
   quick.push("lrs+1002_1:128_au=on:cnfonf=off:fde=unused:fe=axiom:prag=on:slsq=on:slsqc=2:sos=on:i=959:si=on:rtra=on_0");
   quick.push("lrs+1002_3:1_au=on:e2e=on:fd=off:fe=axiom:sos=on:i=2294:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_au=on:av=off:e2e=on:kws=inv_precedence:nwc=10.0:sos=on:i=1240:si=on:rtra=on_0");
   quick.push("ott+1010_3:2_acc=on:au=on:cnfonf=off:fsr=off:ins=3:nm=40:ntd=on:s2a=on:s2agt=60:slsq=on:i=2032:si=on:rtra=on_0");
   quick.push("dis+1002_1:2_au=on:av=off:cnfonf=off:fe=off:s2a=on:sos=on:i=1247:si=on:rtra=on_0");
   quick.push("dis+10_1:1_nwc=3.0:sd=2:ss=axioms:i=175:si=on:rtra=on_0");
   quick.push("lrs+10_1:8_au=on:cnfonf=lazy_pi_sigma_gen:sd=2:sos=all:ss=axioms:st=1.5:i=281:si=on:rtra=on_0");
   quick.push("dis+10_1:8_fsr=off:hud=5:nm=16:prag=on:sd=1:sos=on:sp=frequency:ss=axioms:i=754:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:erd=off:fd=off:fde=none:sos=all:ss=axioms:i=549:si=on:rtra=on_0");
   quick.push("ott+10_1:1_kws=arity:prag=on:sd=1:sos=all:ss=axioms:st=3.0:i=469:si=on:rtra=on_0");
   quick.push("dis+10_1:1_av=off:cnfonf=off:prag=on:sd=2:sos=all:ss=axioms:i=793:si=on:rtra=on_0");
   quick.push("lrs+1002_1:32_au=on:avsq=on:sd=1:sgt=16:sos=on:ss=axioms:st=2.0:i=405:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_au=on:ntd=on:s2a=on:sfv=off:ss=axioms:i=971:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_erd=off:fe=off:ins=3:plsq=on:sos=on:i=398:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:cnfonf=conj_eager:fe=axiom:sd=1:ss=axioms:i=1807:si=on:rtra=on_0");
   quick.push("lrs+1002_1:5_acc=on:avsq=on:avsqr=1,16:fe=axiom:prag=on:sd=1:ss=axioms:st=4.0:i=293:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:bd=off:cnfonf=off:fd=off:fe=axiom:sd=2:sgt=8:sp=reverse_frequency:ss=axioms:i=505:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cbe=off:fe=off:nwc=10.0:sd=1:sos=on:ss=axioms:st=1.5:i=567:si=on:rtra=on_0");
   quick.push("lrs+10_1:128_c=on:sac=on:sos=on:ss=axioms:i=672:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_acc=on:au=on:avsq=on:bd=off:cnfonf=off:fe=off:sd=2:ss=axioms:st=2.0:i=1062:si=on:rtra=on_0");
   quick.push("dis+21_1:1_au=on:cs=on:fde=unused:ntd=on:nwc=10.0:sac=on:sd=1:sgt=10:sos=on:ss=axioms:i=891:si=on:rtra=on_0");
   quick.push("lrs+31_1:1024_apa=on:au=on:cnfonf=off:e2e=on:fsr=off:sd=2:sgt=4:sos=on:ss=axioms:i=628:si=on:rtra=on_0");
  // Improves by expected 83.38577641685194 probs costing 19850 Mi
  // Sub-schedule for 30000Mi strat cap / 30000Mi overall limit
   quick.push("lrs+10_1:1_au=on:fe=axiom:plsq=on:plsqr=32,1:sos=all:ss=axioms:i=1826:si=on:rtra=on_0");
   quick.push("dis+1002_1:8_av=off:fd=off:fsr=off:prag=on:sos=on:ss=axioms:i=423:si=on:rtra=on_0");
   quick.push("dis+10_3:1_au=on:e2e=on:fsr=off:sd=1:sgt=16:ss=axioms:i=799:si=on:rtra=on_0");
   quick.push("ott+1002_1:8_au=on:bd=off:cbe=off:e2e=on:fd=off:inj=on:nicw=on:sd=2:sos=on:sp=reverse_arity:ss=axioms:st=2.0:i=2432:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_au=on:fe=off:kws=precedence:sos=on:sp=frequency:i=2599:si=on:rtra=on_0");
   quick.push("dis+1002_1:3_au=on:fsr=off:sd=1:sgt=16:sos=on:ss=axioms:i=649:si=on:rtra=on_0");
   quick.push("dis+10_1:16_bd=preordered:cnfonf=lazy_pi_sigma_gen:sos=on:ss=axioms:st=1.2:i=495:si=on:rtra=on_0");
   quick.push("lrs+1010_16:1_au=on:av=off:bd=off:cond=fast:nm=2:s2a=on:s2agt=40:sos=all:spb=non_intro:i=834:si=on:rtra=on_0");
   quick.push("dis+1002_8:1_au=on:fde=none:s2a=on:slsq=on:i=3477:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_av=off:cnfonf=off:fs=off:fsr=off:ins=3:kws=precedence:sd=2:sp=reverse_arity:ss=axioms:sup=off:i=408:si=on:rtra=on_0");
   quick.push("dis+1010_2:1_acc=on:au=on:avsq=on:avsqr=1,2:bd=off:bs=unit_only:fe=axiom:sp=const_max:i=2235:si=on:rtra=on_0");
   quick.push("lrs-1002_1:64_bd=off:fde=none:fe=off:hud=10:sos=on:i=586:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bd=off:fe=off:kws=precedence:sos=on:sp=const_max:ss=axioms:i=547:si=on:rtra=on_0");
   quick.push("dis+1002_2:3_amm=off:au=on:fsr=off:nwc=7.0:s2a=on:s2agt=16:ss=axioms:st=3.0:i=611:si=on:rtra=on_0");
   quick.push("lrs+1004_1:1_au=on:av=off:bd=off:plsq=on:plsqc=1:plsqr=32,1:sos=on:ss=axioms:st=2.0:i=399:si=on:rtra=on_0");
   quick.push("lrs-1002_8:1_av=off:bd=off:bs=unit_only:e2e=on:fe=axiom:prag=on:sos=on:ss=axioms:st=3.0:i=1521:si=on:rtra=on_0");
   quick.push("lrs+10_1:128_au=on:bd=off:e2e=on:fsr=off:nwc=10.0:sac=on:sos=all:ss=axioms:st=3.0:i=678:si=on:rtra=on_0");
   quick.push("ott+10_1:1_nwc=2.0:sd=1:sgt=64:sos=all:ss=axioms:i=695:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:av=off:e2e=on:sd=1:sos=all:sp=const_frequency:ss=axioms:i=589:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:av=off:sd=2:sgt=64:sos=all:ss=axioms:i=4566:si=on:rtra=on_0");
   quick.push("lrs+1002_1:4_au=on:av=off:bd=off:e2e=on:fd=off:fsr=off:s2a=on:sos=on:i=800:si=on:rtra=on_0");
   quick.push("dis-1002_1:1_au=on:cnfonf=off:e2e=on:nm=16:plsq=on:plsqr=1,2:sac=on:sos=on:sp=reverse_frequency:ss=axioms:i=2241:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:avsq=on:bd=off:fd=off:fe=axiom:fsr=off:sac=on:sos=on:i=528:si=on:rtra=on_0");
  // Improves by expected 50.792548623271934 probs costing 29915 Mi
  // Sub-schedule for 60000Mi strat cap / 60000Mi overall limit
   quick.push("lrs+1002_1:1_piset=or:prag=on:s2a=on:sos=on:ss=axioms:i=1425:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1024_au=on:e2e=on:fe=off:sos=on:ss=axioms:i=494:si=on:rtra=on_0");
   quick.push("dis+2_1:1_au=on:av=off:bd=off:fd=off:sos=on:sp=const_frequency:i=1750:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:bd=off:fde=none:kws=frequency:plsq=on:plsqc=1:plsqr=32,1:sac=on:sos=on:i=434:si=on:rtra=on_0");
   quick.push("ott+21_1:1_bd=preordered:fd=off:fe=off:fs=off:fsr=off:sos=on:i=377:si=on:rtra=on_0");
   quick.push("dis+21_1:1_av=off:cnfonf=off:prag=on:s2a=on:sos=on:i=484:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_au=on:e2e=on:er=filter:hud=10:kws=precedence:sos=on:sp=weighted_frequency:ss=axioms:st=3.0:uhcvi=on:i=3504:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:avsq=on:avsqc=1:bd=off:c=on:sac=on:sd=1:sos=all:ss=axioms:st=2.0:i=3204:si=on:rtra=on_0");
   quick.push("dis+2_1:32_au=on:kws=precedence:sp=weighted_frequency:ss=axioms:tgt=ground:i=446:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_erd=off:fe=axiom:hud=10:lma=on:sfv=off:slsq=on:sos=all:i=397:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_anc=all:au=on:bd=off:cnfonf=off:fd=off:fs=off:fsr=off:nwc=5.0:sac=on:sos=on:ss=axioms:i=2030:si=on:rtra=on_0");
   quick.push("dis+32_2:1_au=on:av=off:cnfonf=lazy_pi_sigma_gen:ntd=on:s2a=on:slsq=on:i=1282:si=on:rtra=on_0");
   quick.push("dis+1002_16:1_au=on:cnfonf=lazy_not_be_gen:fde=unused:piset=not:sd=1:slsq=on:ss=axioms:st=3.0:i=1778:si=on:rtra=on_0");
   quick.push("dis+10_1:1_av=off:cnfonf=lazy_not_be_gen:s2a=on:slsq=on:i=1059:si=on:rtra=on_0");
   quick.push("lrs+1002_3:2_au=on:bsr=unit_only:hud=10:ntd=on:piset=all_but_not_eq:s2a=on:s2at=7.0:sd=2:sos=all:ss=axioms:i=2194:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_cnfonf=lazy_simp:fe=axiom:hfsq=on:ntd=on:sd=1:sgt=32:ss=axioms:i=456:si=on:rtra=on_0");
   quick.push("ott+10_1:2_ins=4:lcm=predicate:nm=6:s2a=on:s2at=-1.0:sac=on:sd=1:sgt=64:sp=weighted_frequency:ss=axioms:st=1.2:i=1498:si=on:rtra=on_0");
   quick.push("ott+10_16:1_br=off:bsr=unit_only:fe=axiom:flr=on:nm=64:sos=on:sp=occurrence:i=1383:si=on:rtra=on_0");
   quick.push("dis+10_5:1_au=on:nwc=10.0:sac=on:sd=1:sos=on:ss=axioms:i=1027:si=on:rtra=on_0");
   quick.push("dis+10_1:50_av=off:cnfonf=off:prag=on:sd=2:sos=on:ss=axioms:st=1.5:i=926:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_cnfonf=lazy_pi_sigma_gen:fe=axiom:s2a=on:s2agt=8:sd=2:sgt=4:ss=axioms:i=355:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_bsr=unit_only:cnfonf=conj_eager:nwc=3.0:sd=1:ss=axioms:i=663:si=on:rtra=on_0");
   quick.push("dis+1002_1:8_avsq=on:avsqr=1,16:e2e=on:s2a=on:ss=axioms:st=3.0:i=358:si=on:rtra=on_0");
   quick.push("dis+10_1:1_acc=on:c=on:cnfonf=off:e2e=on:nm=32:nwc=10.0:sgt=8:ss=axioms:i=493:si=on:rtra=on_0");
   quick.push("lrs+10_1:8_au=on:cnfonf=lazy_pi_sigma_gen:sd=2:sos=all:ss=axioms:st=1.5:i=418:si=on:rtra=on_0");
   quick.push("ott+1010_8:1_atotf=0.2:au=on:bsr=unit_only:cha=on:e2e=on:fsr=off:sd=1:sp=unary_first:ss=axioms:st=4.0:i=836:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_fe=off:prag=on:sd=1:sos=all:ss=axioms:st=2.5:i=308:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:fd=off:sd=1:sgt=16:sos=all:ss=axioms:i=3033:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_au=on:cnfonf=conj_eager:sd=1:sgt=100:ss=axioms:i=1662:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:sgt=4:sos=on:ss=axioms:i=407:si=on:rtra=on_0");
   quick.push("lrs+1010_5:1_au=on:cbe=off:s2a=on:s2agt=32:sac=on:i=3644:si=on:rtra=on_0");
   quick.push("dis+10_1:2_cnfonf=off:fsr=off:sp=unary_first:ss=axioms:st=1.5:i=663:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_e2e=on:fde=none:nwc=10.0:sd=1:sgt=16:sos=all:ss=axioms:i=251:si=on:rtra=on_0");
   quick.push("ott+10_1:1_fsr=off:hfaw=0:hfsq=on:hfsql=off:hfsqr=4,1:ins=3:kws=precedence:ntd=on:sp=frequency:i=813:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_apa=on:bd=off:bs=unit_only:cnfonf=off:fd=off:fsr=off:hud=3:ins=3:prag=on:sd=2:sgt=8:sos=on:ss=axioms:i=1144:si=on:rtra=on_0");
   quick.push("lrs+10_1:4_av=off:bsr=unit_only:e2e=on:fd=preordered:prag=on:sos=all:sp=const_frequency:i=3763:si=on:rtra=on_0");
   quick.push("dis+10_1:1_hud=10:prag=on:s2a=on:s2at=1.2:sac=on:sos=all:i=1345:si=on:rtra=on_0");
   quick.push("dis+10_1:1_acc=on:apa=on:au=on:avsq=on:avsqr=561497,524288:cnfonf=off:e2e=on:s2a=on:s2agt=64:s2at=2.0:ss=axioms:i=1956:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bd=off:erd=off:sos=on:i=354:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:e2e=on:fde=none:sd=2:sos=all:ss=axioms:i=347:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_aac=none:e2e=on:fsr=off:nm=4:prag=on:sac=on:sd=1:sos=on:ss=axioms:st=4.0:i=730:si=on:rtra=on_0");
   quick.push("lrs+1002_1:8_au=on:ins=2:sd=1:sos=on:ss=axioms:i=435:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_cnfonf=off:s2a=on:s2agt=32:sd=1:ss=axioms:st=6.0:i=401:si=on:rtra=on_0");
   quick.push("lrs+10_3:1_au=on:e2e=on:ins=3:sd=1:sos=all:ss=axioms:i=378:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:avsq=on:avsqr=1,6:bsr=unit_only:nm=2:nwc=2.0:sac=on:sos=all:ss=axioms:i=756:si=on:rtra=on_0");
   quick.push("lrs+1002_1:128_bd=off:fe=axiom:hud=19:sac=on:sos=on:tnu=1:i=722:si=on:rtra=on_0");
   quick.push("dis+21_1:4_au=on:ntd=on:s2a=on:s2agt=32:s2at=1.2:slsq=on:slsqc=1:i=776:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_au=on:cnfonf=off:fs=off:fsr=off:sd=10:sos=on:ss=axioms:st=5.0:i=1711:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_fde=none:sd=1:sos=on:ss=axioms:st=2.0:i=406:si=on:rtra=on_0");
   quick.push("lrs+4_1:10_awrs=converge:awrsf=500:bd=off:kws=inv_frequency:sd=1:ss=axioms:st=3.0:tgt=ground:i=1137:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_acc=model:avsq=on:fe=axiom:fsr=off:nm=16:piset=pi_sigma:prag=on:sd=2:sgt=16:sp=weighted_frequency:ss=axioms:i=3579:si=on:rtra=on_0");
  // Improves by expected 51.41792201759229 probs costing 59941 Mi
  // Sub-schedule for 120000Mi strat cap / 120000Mi overall limit
   quick.push("lrs+1010_16:1_acc=on:au=on:e2e=on:nm=32:sac=on:sd=1:sos=on:ss=axioms:st=5.0:i=4879:si=on:rtra=on_0");
   quick.push("lrs+21_1:64_au=on:cnfonf=lazy_pi_sigma_gen:fsr=off:kws=frequency:s2at=5.0:slsq=on:slsqc=1:i=1100:si=on:rtra=on_0");
   quick.push("dis+1002_1:8_av=off:fd=off:fsr=off:prag=on:sos=on:ss=axioms:i=773:si=on:rtra=on_0");
   quick.push("lrs+10_8:1_au=on:bet=on:c=on:cnfonf=off:lcm=reverse:piset=small_set:sd=1:sp=reverse_frequency:ss=axioms:i=364:si=on:rtra=on_0");
   quick.push("dis+1002_1:1024_av=off:e2e=on:fe=axiom:sos=on:sp=unary_first:i=2641:si=on:rtra=on_0");
   quick.push("lrs+10_1:128_au=on:bd=off:cnfonf=off:plsq=on:plsqr=32,1:sac=on:sos=all:i=2281:si=on:rtra=on_0");
   quick.push("ott+1002_1:8_au=on:bd=off:cbe=off:e2e=on:fd=off:inj=on:nicw=on:sd=2:sos=on:sp=reverse_arity:ss=axioms:st=2.0:i=2421:si=on:rtra=on_0");
   quick.push("dis+1004_1:4_fde=none:sd=1:sgt=32:ss=axioms:tgt=ground:i=569:si=on:rtra=on_0");
   quick.push("lrs+10_2:3_au=on:cnfonf=lazy_pi_sigma_gen:fe=off:kws=inv_arity:sd=2:sp=reverse_arity:ss=axioms:st=3.0:tgt=full:i=947:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:bd=off:fd=off:fde=none:sos=all:i=1670:si=on:rtra=on_0");
   quick.push("lrs+10_8:1_au=on:av=off:cnfonf=lazy_pi_sigma_gen:fsr=off:nwc=6.0:s2a=on:s2agt=16:i=4110:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_ins=2:nm=4:prag=on:sac=on:sd=1:sos=on:spb=goal_then_units:ss=axioms:i=986:si=on:rtra=on_0");
   quick.push("lrs+10_1:5_cnfonf=off:e2e=on:er=known:hud=15:inj=on:sd=1:sgt=40:ss=axioms:tnu=9:i=2044:si=on:rtra=on_0");
   quick.push("lrs+21_1:1024_au=on:nwc=10.0:piset=small_set:sac=on:sfv=off:sos=on:sp=unary_frequency:i=1868:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bd=off:e2e=on:sd=1:sos=on:sp=frequency:ss=axioms:i=1081:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:avsq=on:e2e=on:sos=on:i=2248:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_au=on:er=filter:fe=off:flr=on:hud=10:ntd=on:nwc=10.0:i=1795:si=on:rtra=on_0");
   quick.push("dis+21_1:8_bd=off:cbe=off:fe=off:kws=inv_arity_squared:plsq=on:plsqc=1:plsqr=375431,1048576:sd=1:ss=axioms:st=3.0:tgt=full:tnu=2:i=592:si=on:rtra=on_0");
   quick.push("dis+21_1:1_au=on:e2e=on:fd=off:fe=off:sos=on:i=2401:si=on:rtra=on_0");
   quick.push("ott+10_5:4_amm=off:apa=on:bd=off:bsr=unit_only:cnfonf=off:cond=fast:fe=off:fsr=off:nm=7:plsq=on:prag=on:sac=on:sfv=off:sos=all:sp=const_frequency:tnu=8:i=1206:si=on:rtra=on_0");
   quick.push("ott+10_1:1_apa=on:bsr=unit_only:cnfonf=off:fe=off:fsr=off:hud=8:ntd=on:prag=on:sos=all:ss=axioms:i=781:si=on:rtra=on_0");
   quick.push("dis+21_1:1_av=off:fe=off:hud=1:kws=inv_precedence:sos=on:i=1125:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bd=off:cnfonf=off:fe=axiom:hud=5:sac=on:sd=1:sos=on:ss=axioms:st=2.0:i=416:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_aac=none:au=on:bd=off:cnfonf=off:fd=off:ntd=on:piset=all_but_not_eq:sos=all:i=587:si=on:rtra=on_0");
   quick.push("lrs-1004_16:1_ins=1:plsq=on:plsqc=1:plsqr=32,1:prag=on:sac=on:sd=1:sos=on:spb=goal_then_units:ss=axioms:st=4.0:i=2524:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1024_au=on:av=off:e2e=on:fe=off:kws=inv_arity:sos=on:sp=unary_frequency:i=679:si=on:rtra=on_0");
   quick.push("dis+1002_1:28_aac=none:plsq=on:plsqc=2:plsqr=8,1:sd=2:sp=frequency:ss=axioms:tgt=ground:i=2092:si=on:rtra=on_0");
   quick.push("dis+21_3:1_au=on:c=on:nwc=3.0:s2a=on:s2agt=64:sd=1:sp=reverse_arity:ss=axioms:st=5.0:i=3412:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_au=on:e2e=on:er=known:sos=all:sp=const_max:ss=axioms:i=640:si=on:rtra=on_0");
   quick.push("dis+1010_1:64_acc=model:au=on:awrs=converge:awrsf=200:nwc=10.0:s2a=on:s2at=1.2:slsq=on:i=2074:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:avsq=on:hfsq=on:hfsqr=5,33:kws=arity_squared:piset=equals:plsq=on:plsql=on:plsqr=1,32:sd=1:sos=all:ss=axioms:st=5.0:i=832:si=on:rtra=on_0");
   quick.push("dis+10_6:1_fs=off:fsr=off:hfsq=on:kws=frequency:ntd=on:prag=on:sd=2:ss=axioms:i=862:si=on:rtra=on_0");
   quick.push("lrs+1002_1:32_avsq=on:fd=off:sos=on:i=1662:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_prag=on:sd=1:sos=on:ss=axioms:st=2.0:i=718:si=on:rtra=on_0");
   quick.push("lrs+10_1:4_anc=all:au=on:fe=off:plsq=on:plsqr=32,1:sac=on:sos=all:ss=axioms:i=1004:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_bd=off:fd=off:hud=10:ntd=on:sgt=16:sos=on:ss=axioms:i=644:si=on:rtra=on_0");
   quick.push("dis+10_1:8_fsr=off:hud=5:nm=16:prag=on:sd=1:sos=on:sp=frequency:ss=axioms:i=812:si=on:rtra=on_0");
   quick.push("lrs+10_3:1_au=on:bd=off:sd=1:sos=on:ss=axioms:st=5.0:i=968:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bd=off:fe=off:kws=precedence:sos=on:sp=const_max:ss=axioms:i=547:si=on:rtra=on_0");
   quick.push("dis+10_1:1_av=off:cnfonf=off:prag=on:sd=2:sos=all:ss=axioms:i=3486:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_aac=none:au=on:cnfonf=off:inj=on:kws=precedence:ntd=on:sos=on:sp=reverse_arity:i=3320:si=on:rtra=on_0");
   quick.push("dis+10_1:14_au=on:fe=axiom:lma=on:nm=2:nwc=5.0:sac=on:sos=all:ss=axioms:i=1526:si=on:rtra=on_0");
   quick.push("lrs+10_5:1_au=on:cbe=off:plsq=on:plsqc=1:plsqr=6694409,65536:i=7208:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:cnfonf=conj_eager:fe=axiom:sd=1:ss=axioms:i=4007:si=on:rtra=on_0");
   quick.push("ott+21_163:29_au=on:fde=unused:lcm=predicate:sos=on:sp=const_frequency:i=1097:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_aac=none:cnfonf=lazy_not_gen:fd=off:sos=on:i=495:si=on:rtra=on_0");
   quick.push("ott+10_1:1_au=on:cnfonf=lazy_gen:hflw=2:hfsq=on:hfsqc=2:hfsqr=4,1:kws=precedence:s2a=on:s2at=1.5:sp=unary_first:i=2708:si=on:rtra=on_0");
   quick.push("dis+10_1:16_acc=model:avsq=on:avsqr=1,16:cnfonf=lazy_not_be_gen:plsq=on:plsqc=1:plsqr=32,1:ss=axioms:i=853:si=on:rtra=on_0");
   quick.push("dis+10_1:10_acc=model:e2e=on:fe=off:s2a=on:s2at=3.0:tgt=full:i=699:si=on:rtra=on_0");
   quick.push("dis+10_16:1_acc=on:au=on:fd=off:fsr=off:hflw=0:hfsq=on:kws=precedence:sd=1:ss=axioms:st=1.5:i=3212:si=on:rtra=on_0");
   quick.push("lrs+10_4:1_hud=1:inj=on:prag=on:s2a=on:sos=all:i=1517:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:nm=2:plsq=on:plsqr=32,1:sos=all:i=4382:si=on:rtra=on_0");
   quick.push("lrs+1002_1:5_acc=on:avsq=on:avsqr=1,16:fe=axiom:prag=on:sd=1:ss=axioms:st=4.0:i=663:si=on:rtra=on_0");
   quick.push("lrs+10_2:1_au=on:c=on:cnfonf=off:e2e=on:fe=off:fsr=off:nwc=5.0:s2a=on:s2agt=100:ss=axioms:i=4502:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_au=on:fsr=off:sac=on:sd=1:sgt=32:sos=all:ss=axioms:i=1380:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bsr=unit_only:e2e=on:sos=on:ss=axioms:st=2.0:i=1514:si=on:rtra=on_0");
   quick.push("lrs+1010_1:8_afp=30:au=on:bd=off:c=on:cbe=off:cnfonf=off:hud=15:nm=30:piset=equals:sd=1:sos=on:ss=axioms:i=481:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_fsr=off:ntd=on:nwc=5.0:prag=on:sos=on:sp=unary_first:i=858:si=on:rtra=on_0");
   quick.push("dis+1010_3:1_au=on:bd=off:cnfonf=lazy_simp:fd=off:fsr=off:sd=3:sgt=20:sp=unary_frequency:ss=axioms:i=861:si=on:rtra=on_0");
   quick.push("dis-1002_1:16_av=off:fe=off:hud=19:nwc=12.0:sos=on:ss=axioms:st=2.0:i=1025:si=on:rtra=on_0");
   quick.push("dis+10_16:1_acc=on:avsq=on:fe=axiom:fsr=off:s2a=on:s2agt=16:s2at=3.0:i=3806:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:cnfonf=off:hfsq=on:ins=2:s2a=on:s2at=1.5:sd=1:ss=axioms:st=3.0:i=617:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_hud=24:plsq=on:sd=1:sos=all:ss=axioms:tnu=1:i=581:si=on:rtra=on_0");
   quick.push("lrs+1002_3:1_au=on:cnfonf=off:fe=off:lcm=reverse:sd=1:sos=on:sp=const_frequency:ss=axioms:i=1125:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_au=on:cnfonf=lazy_pi_sigma_gen:ntd=on:nwc=10.0:slsq=on:slsqc=1:sp=unary_frequency:uhcvi=on:i=4051:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:fd=off:nm=20:nwc=10.0:plsq=on:s2a=on:s2agt=64:ss=axioms:st=5.0:i=702:si=on:rtra=on_0");
   quick.push("dis+10_1:1024_au=on:cnfonf=lazy_pi_sigma_gen:ins=1:tgt=ground:i=644:si=on:rtra=on_0");
   quick.push("dis-1002_1:1_av=off:bs=unit_only:fe=axiom:hud=10:prag=on:sos=on:sp=const_frequency:ss=axioms:tnu=2:i=974:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_aac=none:bd=off:e2e=on:kws=inv_frequency:sos=all:ss=axioms:i=1008:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:avsq=on:bd=off:cnfonf=lazy_pi_sigma_gen:fd=off:sos=on:i=876:si=on:rtra=on_0");
   quick.push("dis+1002_1:4_aac=none:bd=off:e2e=on:fe=off:fsr=off:prag=on:sos=on:i=767:si=on:rtra=on_0");
   quick.push("dis+10_1:16_awrs=converge:e2e=on:fe=off:nwc=10.0:s2a=on:s2at=4.0:sd=2:ss=axioms:st=2.0:i=672:si=on:rtra=on_0");
  // Improves by expected 44.20607043074075 probs costing 119900 Mi
  // Sub-schedule for 240000Mi strat cap / 240000Mi overall limit
   quick.push("lrs+10_1:1_au=on:fe=axiom:plsq=on:plsqr=32,1:sos=all:ss=axioms:i=4406:si=on:rtra=on_0");
   quick.push("ott+2_8:1_au=on:awrs=converge:e2e=on:fsr=off:hud=10:ins=3:ntd=on:s2at=2.5:slsq=on:slsqc=1:i=4617:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_piset=or:prag=on:s2a=on:sos=on:ss=axioms:i=3296:si=on:rtra=on_0");
   quick.push("ott+1010_3:1_aac=none:cbe=off:fsr=off:kws=inv_frequency:nwc=4.0:tnu=1:i=2128:si=on:rtra=on_0");
   quick.push("lrs+1010_4:1_amm=sco:ins=3:ss=axioms:st=1.5:i=3408:si=on:rtra=on_0");
   quick.push("dis+10_1:8_au=on:bd=off:cnfonf=off:e2e=on:fde=none:lma=on:sgt=5:sos=all:ss=axioms:i=3184:si=on:rtra=on_0");
   quick.push("dis+21_1:1_av=off:cnfonf=off:prag=on:s2a=on:sos=on:i=1304:si=on:rtra=on_0");
   quick.push("lrs+21_1:128_av=off:e2e=on:hud=1:prag=on:sd=2:sgt=10:sos=all:ss=axioms:i=3585:si=on:rtra=on_0");
   quick.push("dis+10_1:1_cnfonf=lazy_not_be_gen:fe=axiom:fs=off:fsr=off:plsq=on:s2a=on:s2at=2.0:sos=all:i=3340:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_anc=all:au=on:bd=off:cnfonf=off:fd=off:fs=off:fsr=off:nwc=5.0:sac=on:sos=on:ss=axioms:i=5830:si=on:rtra=on_0");
   quick.push("dis+10_1:16_au=on:cnfonf=off:fe=off:plsq=on:plsqc=1:plsqr=32,1:rawr=on:tgt=ground:i=1020:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:ins=2:ixr=off:nm=2:nwc=3.0:sac=on:sos=on:i=1087:si=on:rtra=on_0");
   quick.push("dis+1002_1:3_atotf=0.2:bd=off:cnfonf=conj_eager:fd=off:fe=off:ins=1:nwc=2.0:plsq=on:plsqc=2:plsqr=32,1:s2a=on:s2agt=4:sos=all:i=1525:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_au=on:av=off:e2e=on:kws=inv_precedence:nwc=10.0:sos=on:i=7200:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bd=off:e2e=on:sd=1:sos=on:sp=frequency:ss=axioms:i=4551:si=on:rtra=on_0");
   quick.push("ott+1010_3:2_acc=on:au=on:cnfonf=off:fsr=off:ins=3:nm=40:ntd=on:s2a=on:s2agt=60:slsq=on:i=14357:si=on:rtra=on_0");
   quick.push("dis+1010_2:1_acc=on:au=on:bd=off:fde=none:hud=15:sgt=4:sp=const_max:ss=axioms:uhcvi=on:i=1095:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_au=on:cnfonf=lazy_gen:nwc=10.0:s2a=on:sp=unary_first:i=9755:si=on:rtra=on_0");
   quick.push("lrs+10_2:1_au=on:awrs=decay:bsr=on:e2e=on:fe=off:nm=40:nwc=10.0:piset=all:sos=all:i=2288:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:cnfonf=lazy_not_gen:nwc=5.0:sos=all:i=1973:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:ins=3:nm=4:sgt=20:sos=all:ss=axioms:i=11085:si=on:rtra=on_0");
   quick.push("dis+1002_16:1_au=on:er=filter:fd=off:fs=off:fsr=off:hud=20:kws=arity:nm=40:nwc=6.0:sd=7:sos=on:ss=axioms:i=491:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:er=known:fe=off:s2a=on:sac=on:sos=on:i=4606:si=on:rtra=on_0");
   quick.push("ott+30_1:1_cnfonf=off:fd=off:nm=4:ntd=on:plsq=on:plsqr=32,1:sac=on:i=2533:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_avsq=on:bsr=unit_only:cnfonf=off:kws=frequency:nm=32:sos=on:sp=const_frequency:i=3838:si=on:rtra=on_0");
   quick.push("lrs+2_1:3_apa=on:au=on:avsq=on:cnfonf=off:fde=unused:fs=off:fsr=off:rawr=on:sos=all:i=901:si=on:rtra=on_0");
   quick.push("dis+10_1:50_av=off:cnfonf=off:prag=on:sd=2:sos=on:ss=axioms:st=1.5:i=828:si=on:rtra=on_0");
   quick.push("lrs+1002_1:16_au=on:av=off:c=on:cbe=off:fe=off:plsq=on:plsqr=263619,8192:sos=on:ss=axioms:i=1835:si=on:rtra=on_0");
   quick.push("ott+1010_2:3_aac=none:afr=on:cnfonf=lazy_gen:fe=axiom:hud=1:nwc=10.0:piset=all_but_not_eq:prag=on:s2a=on:s2at=3.0:i=1901:si=on:rtra=on_0");
   quick.push("dis+1010_1:64_acc=model:au=on:awrs=converge:awrsf=200:nwc=10.0:s2a=on:s2at=1.2:slsq=on:i=2007:si=on:rtra=on_0");
   quick.push("ott+1002_5:1_cond=fast:e2e=on:fe=off:hud=15:piset=all_but_not_eq:s2a=on:s2agt=100:s2at=5.0:sac=on:sos=on:i=802:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:bd=off:cnfonf=off:fsr=off:sd=1:sgt=32:ss=axioms:i=1817:si=on:rtra=on_0");
   quick.push("ott+1010_452:41_au=on:fsr=off:hfaw=0:hfsq=on:hfsqc=10:ins=3:kws=inv_frequency:nm=2:rawr=on:s2a=on:s2at=5.0:s2pl=on:sac=on:uhcvi=on:i=2186:si=on:rtra=on_0");
   quick.push("lrs+10_4:1_apa=on:av=off:cnfonf=off:piset=pi_sigma:prag=on:slsq=on:slsqr=2,1:ss=axioms:i=5341:si=on:rtra=on_0");
   quick.push("dis+21_8:1_acc=model:au=on:avsq=on:avsqr=1,8:bsr=on:e2e=on:fd=off:fe=off:ixr=off:ntd=on:nwc=5.0:plsq=on:plsqc=1:plsqr=4056251,32768:s2a=on:i=1946:si=on:rtra=on_0");
   quick.push("ott+1010_8:1_atotf=0.2:au=on:bsr=unit_only:cha=on:e2e=on:fsr=off:sd=1:sp=unary_first:ss=axioms:st=4.0:i=14118:si=on:rtra=on_0");
   quick.push("lrs+21_1:1024_au=on:chr=on:erd=off:fe=axiom:sos=all:ss=axioms:i=1892:si=on:rtra=on_0");
   quick.push("lrs+10_2:1_bd=off:cbe=off:fe=axiom:flr=on:prag=on:sd=2:ss=axioms:st=1.5:i=1162:si=on:rtra=on_0");
   quick.push("lrs+10_1:2_e2e=on:sd=1:ss=axioms:st=3.0:i=1016:si=on:rtra=on_0");
   quick.push("lrs+1004_1:1_au=on:av=off:bd=off:plsq=on:plsqc=1:plsqr=32,1:sos=on:ss=axioms:st=2.0:i=1141:si=on:rtra=on_0");
   quick.push("dis+10_16:1_hud=1:lma=on:ntd=on:prag=on:sos=all:sp=occurrence:ss=axioms:i=1830:si=on:rtra=on_0");
   quick.push("dis+1010_2:3_acc=on:bd=off:cnfonf=off:fe=axiom:kws=inv_arity_squared:piset=equals:prag=on:sd=1:sp=reverse_arity:ss=axioms:tgt=ground:i=1674:si=on:rtra=on_0");
   quick.push("ott+4_1:1_cbe=off:cnfonf=lazy_not_be_gen:hud=20:irw=on:nwc=5.0:piset=all:plsq=on:plsqr=32,1:prag=on:sos=all:sp=occurrence:i=2039:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bsr=unit_only:s2a=on:sos=all:ss=axioms:i=802:si=on:rtra=on_0");
   quick.push("dis+10_1:16_acc=model:avsq=on:avsqr=1,16:cnfonf=lazy_not_be_gen:plsq=on:plsqc=1:plsqr=32,1:ss=axioms:i=2250:si=on:rtra=on_0");
   quick.push("lrs+20_1:4_au=on:bd=off:e2e=on:slsq=on:slsqr=1,8:sos=on:i=4703:si=on:rtra=on_0");
   quick.push("dis+10_1:64_au=on:cnfonf=off:fde=none:ins=2:nm=6:sos=on:i=1929:si=on:rtra=on_0");
   quick.push("ott+1010_8:1_apa=on:atotf=0.3:au=on:cnfonf=off:s2a=on:s2agt=16:sgt=8:sos=on:sp=frequency:ss=axioms:i=4669:si=on:rtra=on_0");
   quick.push("dis+1010_1:3_bd=preordered:cnfonf=lazy_simp:nwc=5.0:s2a=on:s2at=3.0:sp=unary_first:i=3446:si=on:rtra=on_0");
   quick.push("dis+1010_3:2_e2e=on:rawr=on:sac=on:sd=1:sos=all:ss=axioms:st=3.0:i=1969:si=on:rtra=on_0");
   quick.push("lrs-1002_8:1_av=off:bd=off:bs=unit_only:e2e=on:fe=axiom:prag=on:sos=on:ss=axioms:st=3.0:i=4393:si=on:rtra=on_0");
   quick.push("lrs+1002_1:7_au=on:cnfonf=off:fe=axiom:ins=2:lecc=0.5:nm=32:sd=1:sgt=64:ss=axioms:i=2917:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_kws=arity:nwc=10.0:prag=on:sd=1:sgt=16:ss=axioms:i=723:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1024_av=off:bd=off:sd=2:sos=on:ss=axioms:st=3.0:i=1277:si=on:rtra=on_0");
   quick.push("ott+10_4:1_cnfonf=lazy_gen:fe=axiom:plsq=on:plsqc=1:plsqr=32,1:s2a=on:s2agt=32:ss=axioms:i=1469:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_av=off:bd=off:cnfonf=off:fe=axiom:hud=5:nwc=10.0:sd=1:sos=on:ss=axioms:st=2.0:i=1156:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_au=on:bd=off:cbe=off:cnfonf=lazy_pi_sigma_gen:fe=off:s2a=on:s2agt=32:i=4604:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cbe=off:fe=off:nwc=10.0:sd=1:sos=on:ss=axioms:st=1.5:i=3044:si=on:rtra=on_0");
   quick.push("ott+1010_1:4_au=on:avsq=on:bsr=on:cnfonf=off:e2e=on:nm=2:sac=on:sos=all:i=13916:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:avsq=on:avsqr=1,6:bsr=unit_only:nm=2:nwc=2.0:sac=on:sos=all:ss=axioms:i=3820:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:bd=off:fd=off:sos=all:ss=axioms:i=2903:si=on:rtra=on_0");
   quick.push("dis-33_1:62_fsr=off:hfsq=on:s2a=on:sac=on:slsq=on:slsqc=1:slsqr=2735097,1048576:i=1308:si=on:rtra=on_0");
   quick.push("dis+10_1:1_alpa=true:atotf=0.4:avsq=on:avsqr=1,16:cnfonf=lazy_pi_sigma_gen:fd=off:fde=unused:fe=axiom:ins=1:s2a=on:s2at=1.5:i=3339:si=on:rtra=on_0");
   quick.push("dis+21_1:1_au=on:cs=on:fde=unused:ntd=on:nwc=10.0:sac=on:sd=1:sgt=10:sos=on:ss=axioms:i=891:si=on:rtra=on_0");
   quick.push("dis+1004_5:1_au=on:fe=off:plsq=on:plsqc=1:plsqr=32,1:sos=on:sp=const_frequency:spb=goal:i=1058:si=on:rtra=on_0");
   quick.push("dis+2_1:1_au=on:cnfonf=off:e2e=on:fe=off:nwc=3.0:s2a=on:s2at=7.0:sp=weighted_frequency:i=2138:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:av=off:sd=2:sgt=64:sos=all:ss=axioms:i=6939:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_acc=model:avsq=on:fe=axiom:fsr=off:nm=16:piset=pi_sigma:prag=on:sd=2:sgt=16:sp=weighted_frequency:ss=axioms:i=14103:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_au=on:nwc=10.0:s2agt=32:s2at=7.0:s2pl=on:sp=frequency:ss=axioms:uhcvi=on:i=3332:si=on:rtra=on_0");
  // Improves by expected 38.33506744983474 probs costing 239967 Mi
  // Sub-schedule for 480000Mi strat cap / 480000Mi overall limit
   quick.push("lrs+10_1:1_au=on:fe=axiom:plsq=on:plsqr=32,1:sos=all:ss=axioms:i=4201:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:av=off:cnfonf=conj_eager:fe=off:nwc=5.0:sp=unary_first:ss=axioms:st=3.0:i=20925:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cnfonf=lazy_not_be_gen:piset=all_but_not_eq:plsq=on:plsqc=1:plsqr=19,2:sac=on:slsq=on:i=6917:si=on:rtra=on_0");
   quick.push("dis+1002_16:1_avsq=on:cbe=off:prag=on:s2a=on:sac=on:i=3537:si=on:rtra=on_0");
   quick.push("lrs+1004_2:3_au=on:c=on:cnfonf=off:ins=2:kws=precedence:ntd=on:sp=reverse_frequency:spb=goal:i=3785:si=on:rtra=on_0");
   quick.push("ott+1002_1:8_au=on:bd=off:cbe=off:e2e=on:fd=off:inj=on:nicw=on:sd=2:sos=on:sp=reverse_arity:ss=axioms:st=2.0:i=20258:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:avsq=on:avsqc=1:bd=off:c=on:sac=on:sd=1:sos=all:ss=axioms:st=2.0:i=7608:si=on:rtra=on_0");
   quick.push("dis+10_1:8_cnfonf=lazy_not_gen:plsq=on:plsqc=1:plsqr=19,2:s2pl=on:sd=1:sp=unary_frequency:ss=axioms:st=4.0:i=6035:si=on:rtra=on_0");
   quick.push("dis+10_1:1_cnfonf=lazy_not_be_gen:fe=axiom:fs=off:fsr=off:plsq=on:s2a=on:s2at=2.0:sos=all:i=3340:si=on:rtra=on_0");
   quick.push("lrs+1002_3:1_au=on:e2e=on:fd=off:fe=axiom:sos=on:i=4637:si=on:rtra=on_0");
   quick.push("dis+10_1:3_aac=none:bd=off:cnfonf=lazy_not_gen:fe=axiom:kws=inv_frequency:nwc=3.0:prag=on:s2a=on:s2at=7.0:i=2787:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:ins=2:ixr=off:nm=2:nwc=3.0:sac=on:sos=on:i=7814:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_bet=on:erd=off:fe=off:hud=10:prag=on:sac=on:sos=all:sp=const_max:i=3587:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:avsq=on:e2e=on:sos=on:i=4358:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:av=off:cnfonf=off:cs=on:fd=off:fde=unused:nm=4:ntd=on:prag=on:sos=all:sp=unary_first:i=4381:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_cnfonf=lazy_pi_sigma_gen:ins=1:ntd=on:plsq=on:sp=const_min:i=3405:si=on:rtra=on_0");
   quick.push("ott-1002_8:1_au=on:bd=off:bsr=unit_only:ntd=on:sac=on:sos=on:sp=reverse_arity:i=5401:si=on:rtra=on_0");
   quick.push("dis+1002_16:1_au=on:er=filter:fd=off:fs=off:fsr=off:hud=20:kws=arity:nm=40:nwc=6.0:sd=7:sos=on:ss=axioms:i=5708:si=on:rtra=on_0");
   quick.push("ott+10_1:4_amm=sco:au=on:nwc=5.0:s2a=on:s2at=3.0:sp=const_max:i=5864:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:er=known:fe=off:s2a=on:sac=on:sos=on:i=4606:si=on:rtra=on_0");
   quick.push("dis+1010_2:3_abs=on:amm=off:atotf=0.4:au=on:avsq=on:fe=axiom:hfsq=on:hfsqc=1:kws=frequency:ntd=on:nwc=3.0:prag=on:s2a=on:i=6978:si=on:rtra=on_0");
   quick.push("lrs+1004_5:1_apa=on:avsq=on:cnfonf=off:e2e=on:fe=axiom:fsr=off:ntd=on:plsq=on:plsqc=1:plsqr=32,1:sp=const_max:i=1958:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_avsq=on:bsr=unit_only:cnfonf=off:kws=frequency:nm=32:sos=on:sp=const_frequency:i=3838:si=on:rtra=on_0");
   quick.push("lrs+10_1:16_atotf=0.3:bsr=on:nm=10:sd=1:sgt=16:slsq=on:slsqc=4:slsqr=1,3:sp=frequency:ss=axioms:tgt=full:i=4750:si=on:rtra=on_0");
   quick.push("ott+1002_1:64_atotf=0.2:au=on:hflw=2:hfsq=on:hfsql=off:hfsqr=1,2:kws=inv_frequency:sos=on:sp=occurrence:i=2036:si=on:rtra=on_0");
   quick.push("lrs+10_16:1_aac=none:au=on:cnfonf=lazy_pi_sigma_gen:s2a=on:slsq=on:slsqr=1,4:i=10956:si=on:rtra=on_0");
   quick.push("dis+2_1:1_av=off:fe=off:prag=on:s2a=on:sos=on:i=3686:si=on:rtra=on_0");
   quick.push("lrs+10_8:1_au=on:e2e=on:s2a=on:s2agt=64:sac=on:sos=on:i=10086:si=on:rtra=on_0");
   quick.push("dis+1010_1:64_acc=model:au=on:awrs=converge:awrsf=200:nwc=10.0:s2a=on:s2at=1.2:slsq=on:i=11839:si=on:rtra=on_0");
   quick.push("lrs+21_5:4_apa=on:c=on:cnfonf=off:er=known:fe=axiom:fs=off:fsr=off:prag=on:sos=on:i=1063:si=on:rtra=on_0");
   quick.push("dis+1010_1:8_au=on:ins=1:sd=1:sos=on:sp=unary_first:ss=axioms:i=3992:si=on:rtra=on_0");
   quick.push("ott+1010_2:1_bs=unit_only:bsr=unit_only:cnfonf=lazy_not_gen:etr=on:fe=off:piset=pi_sigma:plsq=on:plsqc=1:plsqr=32,1:sos=all:i=12001:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_au=on:cnfonf=off:nm=32:ntd=on:nwc=10.0:i=3901:si=on:rtra=on_0");
   quick.push("ott+1010_2:1_e2e=on:fsr=off:hud=1:ins=3:sd=1:ss=axioms:st=3.0:i=2736:si=on:rtra=on_0");
   quick.push("lrs+1010_1:128_apa=on:bd=off:cnfonf=off:e2e=on:prag=on:sd=1:sos=on:ss=axioms:st=2.0:i=6312:si=on:rtra=on_0");
   quick.push("lrs+10_4:1_apa=on:av=off:cnfonf=off:piset=pi_sigma:prag=on:slsq=on:slsqr=2,1:ss=axioms:i=17621:si=on:rtra=on_0");
   quick.push("lrs+21_4:1_au=on:fe=axiom:ins=3:ntd=on:nwc=10.0:i=11226:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_cnfonf=off:erd=off:hud=21:ins=2:plsq=on:plsqr=32,1:sac=on:sos=on:i=7700:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_av=off:fsr=off:plsq=on:plsqr=32,1:sd=1:sos=on:ss=axioms:i=4520:si=on:rtra=on_0");
   quick.push("lrs+21_1:1024_au=on:chr=on:erd=off:fe=axiom:sos=all:ss=axioms:i=1892:si=on:rtra=on_0");
   quick.push("lrs+1004_2:3_au=on:c=on:cnfonf=off:fe=off:ins=1:sd=1:sgt=16:ss=axioms:i=6080:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_aac=none:au=on:cnfonf=off:inj=on:kws=precedence:ntd=on:sos=on:sp=reverse_arity:i=3320:si=on:rtra=on_0");
   quick.push("lrs+10_5:1_au=on:cbe=off:plsq=on:plsqc=1:plsqr=6694409,65536:i=29072:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_acc=on:avsq=on:avsqr=1,16:c=on:cnfonf=off:fe=axiom:i=2145:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_e2e=on:fde=none:nwc=10.0:sd=1:sgt=16:sos=all:ss=axioms:i=2290:si=on:rtra=on_0");
   quick.push("lrs+10_4:1_au=on:bd=off:cnfonf=lazy_pi_sigma_gen:ss=axioms:i=6538:si=on:rtra=on_0");
   quick.push("dis+2_12:1_afp=100000:afq=1.0:apa=on:au=on:c=on:cnfonf=off:fe=off:ins=2:nm=32:sos=all:sp=occurrence:i=1742:si=on:rtra=on_0");
   quick.push("dis-1004_16:1_awrs=converge:cnfonf=conj_eager:fe=off:fsr=off:nwc=5.0:plsq=on:plsqc=1:plsqr=4709875,524288:sp=const_frequency:i=9984:si=on:rtra=on_0");
   quick.push("lrs+10_1:1024_aac=none:anc=all:au=on:bd=off:fd=off:fe=off:kws=precedence:piset=pi_sigma:plsq=on:plsqr=4689123,65536:sos=all:sp=unary_frequency:i=7093:si=on:rtra=on_0");
   quick.push("lrs+1666_1:1_fe=axiom:prag=on:sos=all:sp=reverse_arity:ss=axioms:i=4712:si=on:rtra=on_0");
   quick.push("lrs+1002_1:64_au=on:e2e=on:fe=off:kws=precedence:ntd=on:sac=on:sp=reverse_arity:tgt=ground:i=1968:si=on:rtra=on_0");
   quick.push("dis+21_1:1_fe=axiom:sd=1:sos=on:ss=axioms:i=1812:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_au=on:cnfonf=off:e2e=on:s2a=on:s2agt=16:slsq=on:i=6205:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_aac=none:cnfonf=lazy_not_be_gen:sos=all:i=5492:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:bd=off:cnfonf=off:fd=off:fe=axiom:sd=2:sgt=8:sp=reverse_frequency:ss=axioms:i=20720:si=on:rtra=on_0");
   quick.push("dis+1002_1:128_acc=on:amm=off:au=on:cha=on:cnfonf=lazy_pi_sigma_gen:fe=off:hflw=2:hfsq=on:hud=10:ntd=on:piset=or:i=1689:si=on:rtra=on_0");
   quick.push("lrs+10_1:4_au=on:kws=inv_frequency:lma=on:sos=all:sp=const_frequency:i=5065:si=on:rtra=on_0");
   quick.push("lrs+10_2:1_au=on:c=on:cnfonf=off:e2e=on:fe=off:fsr=off:nwc=5.0:s2a=on:s2agt=100:ss=axioms:i=7852:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_au=on:bsr=unit_only:cbe=off:fd=off:fsr=off:sos=on:ss=axioms:i=2910:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_au=on:fsr=off:sac=on:sd=1:sgt=32:sos=all:ss=axioms:i=2138:si=on:rtra=on_0");
   quick.push("dis+21_8:1_avsq=on:avsqr=1,16:cnfonf=off:fd=off:prag=on:s2a=on:slsq=on:slsqc=2:slsqr=2,31:sos=all:i=7099:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cbe=off:fe=off:nwc=10.0:sd=1:sos=on:ss=axioms:st=1.5:i=8702:si=on:rtra=on_0");
   quick.push("lrs+10_1:4_av=off:bd=off:ntd=on:prag=on:sos=all:sp=occurrence:i=5212:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_acc=on:au=on:avsq=on:bd=off:cnfonf=off:fe=off:sd=2:ss=axioms:st=2.0:i=6777:si=on:rtra=on_0");
   quick.push("dis+1010_3:1_au=on:bd=off:cnfonf=lazy_simp:fd=off:fsr=off:sd=3:sgt=20:sp=unary_frequency:ss=axioms:i=8801:si=on:rtra=on_0");
   quick.push("ott+1010_3:1_av=off:ins=3:sos=all:ss=axioms:i=10813:si=on:rtra=on_0");
   quick.push("ott+10_16:1_amm=off:au=on:avsq=on:cnfonf=lazy_not_gen_be_off:piset=equals:s2a=on:s2at=3.0:i=8464:si=on:rtra=on_0");
   quick.push("dis+3_10:23_bd=off:fde=none:fe=off:nwc=5.0:sac=on:sfv=off:sp=occurrence:i=14070:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cbe=off:cnfonf=off:piset=equals:sd=1:sos=all:ss=axioms:i=11466:si=on:rtra=on_0");
   quick.push("dis+2_1:40_au=on:av=off:fd=off:hfsq=on:hfsqr=1,32:nm=2:sos=on:sp=const_min:i=11391:si=on:rtra=on_0");
  // Improves by expected 33.334496597666266 probs costing 479797 Mi
  // Sub-schedule for 960000Mi strat cap / 960000Mi overall limit
   quick.push("lrs+10_1:1_au=on:fe=axiom:plsq=on:plsqr=32,1:sos=all:ss=axioms:i=4201:si=on:rtra=on_0");
   quick.push("lrs+10_1:4_av=off:fd=off:fsr=off:hud=1:plsq=on:plsqr=32,1:prag=on:sd=2:sos=all:ss=axioms:st=2.0:i=13662:si=on:rtra=on_0");
   quick.push("dis+10_1:1_nwc=10.0:prag=on:s2a=on:s2agt=64:sp=unary_first:uhcvi=on:i=12648:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_bd=off:cnfonf=off:fd=off:fe=off:ntd=on:prag=on:sos=all:i=9759:si=on:rtra=on_0");
   quick.push("ott+1002_1:8_au=on:bd=off:cbe=off:e2e=on:fd=off:inj=on:nicw=on:sd=2:sos=on:sp=reverse_arity:ss=axioms:st=2.0:i=16940:si=on:rtra=on_0");
   quick.push("ott+10_8:1_apa=on:au=on:av=off:cnfonf=off:nwc=10.0:sp=reverse_arity:ss=axioms:i=50131:si=on:rtra=on_0");
   quick.push("dis+10_1:1_cnfonf=lazy_not_be_gen:fe=axiom:fs=off:fsr=off:plsq=on:s2a=on:s2at=2.0:sos=all:i=3340:si=on:rtra=on_0");
   quick.push("lrs+10_8:1_au=on:av=off:cnfonf=lazy_pi_sigma_gen:fsr=off:nwc=6.0:s2a=on:s2agt=16:i=24878:si=on:rtra=on_0");
   quick.push("ott+2_1:1_anc=all_dependent:cnfonf=lazy_pi_sigma_gen:fe=off:nwc=10.0:s2a=on:s2agt=100:i=39415:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1024_au=on:av=off:ntd=on:sos=on:sp=frequency:ss=axioms:st=5.0:i=3525:si=on:rtra=on_0");
   quick.push("dis+21_1:16_avsq=on:avsqr=3,1:bd=preordered:cha=on:cnfonf=off:e2e=on:fsr=off:sos=on:sp=weighted_frequency:tnu=2:i=3358:si=on:rtra=on_0");
   quick.push("lrs+10_2:1_au=on:awrs=decay:bsr=on:e2e=on:fe=off:nm=40:nwc=10.0:piset=all:sos=all:i=9251:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:av=off:cnfonf=off:cs=on:fd=off:fde=unused:nm=4:ntd=on:prag=on:sos=all:sp=unary_first:i=9543:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_au=on:av=off:bd=preordered:bsr=on:c=on:nwc=10.0:s2a=on:ss=axioms:i=20296:si=on:rtra=on_0");
   quick.push("lrs+1002_3:2_au=on:bsr=unit_only:hud=10:ntd=on:piset=all_but_not_eq:s2a=on:s2at=7.0:sd=2:sos=all:ss=axioms:i=16038:si=on:rtra=on_0");
   quick.push("lrs-1004_1:1_c=on:cnfonf=off:nm=2:plsq=on:plsqc=1:plsqr=14,1:sp=const_frequency:ss=axioms:i=9327:si=on:rtra=on_0");
   quick.push("dis+1002_16:1_au=on:er=filter:fd=off:fs=off:fsr=off:hud=20:kws=arity:nm=40:nwc=6.0:sd=7:sos=on:ss=axioms:i=5708:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:e2e=on:nm=0:sos=all:sp=const_frequency:i=7666:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:er=known:fe=off:s2a=on:sac=on:sos=on:i=4146:si=on:rtra=on_0");
   quick.push("dis+1010_2:3_abs=on:amm=off:atotf=0.4:au=on:avsq=on:fe=axiom:hfsq=on:hfsqc=1:kws=frequency:ntd=on:nwc=3.0:prag=on:s2a=on:i=6978:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_c=on:cnfonf=conj_eager:ins=3:nwc=4.0:plsq=on:plsqc=1:plsqr=15179,262144:sac=on:sd=1:ss=axioms:i=9037:si=on:rtra=on_0");
   quick.push("lrs+1004_5:1_apa=on:avsq=on:cnfonf=off:e2e=on:fe=axiom:fsr=off:ntd=on:plsq=on:plsqc=1:plsqr=32,1:sp=const_max:i=4559:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_avsq=on:bsr=unit_only:cnfonf=off:kws=frequency:nm=32:sos=on:sp=const_frequency:i=4544:si=on:rtra=on_0");
   quick.push("ott+10_1:1_au=on:avsq=on:avsqr=1,16:c=on:cnfonf=off:sd=1:sos=all:ss=axioms:st=5.0:i=2889:si=on:rtra=on_0");
   quick.push("lrs+1010_8:1_bs=unit_only:cnfonf=lazy_not_gen_be_off:fe=off:fsr=off:hfsq=on:lecc=1.5:nwc=7.0:piset=equals:s2a=on:s2agt=10:sac=on:i=8945:si=on:rtra=on_0");
   quick.push("dis+1010_2:1_acc=on:au=on:avsq=on:avsqr=1,2:bd=off:bs=unit_only:fe=axiom:sp=const_max:i=107085:si=on:rtra=on_0");
   quick.push("ott+1010_2:3_aac=none:afr=on:cnfonf=lazy_gen:fe=axiom:hud=1:nwc=10.0:piset=all_but_not_eq:prag=on:s2a=on:s2at=3.0:i=38728:si=on:rtra=on_0");
   quick.push("ott+10_3:1_c=on:cnfonf=lazy_not_be_gen:fsr=off:ntd=on:sd=10:sos=all:ss=axioms:st=2.0:i=8601:si=on:rtra=on_0");
   quick.push("dis+1010_1:64_acc=model:au=on:awrs=converge:awrsf=200:nwc=10.0:s2a=on:s2at=1.2:slsq=on:i=16649:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cnfonf=off:e2e=on:hud=10:ins=2:plsq=on:plsqc=1:plsqr=32,1:s2a=on:sac=on:sos=on:i=26547:si=on:rtra=on_0");
   quick.push("lrs+1002_1:32_avsq=on:fd=off:sos=on:i=15956:si=on:rtra=on_0");
   quick.push("dis+1010_4:1_au=on:cnfonf=lazy_pi_sigma_gen:sac=on:sgt=8:ss=axioms:i=6334:si=on:rtra=on_0");
   quick.push("dis+10_1:3_au=on:cnfonf=lazy_pi_sigma_gen:fe=axiom:nwc=5.0:s2a=on:s2at=3.0:sac=on:sp=const_max:i=3701:si=on:rtra=on_0");
   quick.push("lrs+1010_5:1_apa=on:au=on:av=off:cnfonf=off:fe=axiom:sos=on:i=7349:si=on:rtra=on_0");
   quick.push("lrs+1010_2:1_au=on:av=off:e2e=on:fe=off:kws=inv_frequency:sos=on:i=8672:si=on:rtra=on_0");
   quick.push("dis+10_1:1_av=off:cnfonf=off:prag=on:sd=2:sos=all:ss=axioms:i=22332:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_aac=none:au=on:cnfonf=off:inj=on:kws=precedence:ntd=on:sos=on:sp=reverse_arity:i=3320:si=on:rtra=on_0");
   quick.push("ott+1004_4:1_av=off:cbe=off:fsr=off:ins=3:kws=inv_frequency:nm=20:prag=on:i=38170:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:cnfonf=off:e2e=on:sos=all:i=9092:si=on:rtra=on_0");
   quick.push("dis+1010_2:3_acc=on:bd=off:cnfonf=off:fe=axiom:kws=inv_arity_squared:piset=equals:prag=on:sd=1:sp=reverse_arity:ss=axioms:tgt=ground:i=4302:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_atotf=0.4:au=on:bsr=unit_only:cbe=off:e2e=on:fe=axiom:sos=on:sp=reverse_arity:i=8305:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bsr=unit_only:s2a=on:sos=all:ss=axioms:i=10056:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bd=off:fe=off:sos=on:sp=unary_first:i=6400:si=on:rtra=on_0");
   quick.push("lrs+20_1:4_au=on:bd=off:e2e=on:slsq=on:slsqr=1,8:sos=on:i=5185:si=on:rtra=on_0");
   quick.push("lrs+10_4:1_hud=1:inj=on:prag=on:s2a=on:sos=all:i=16774:si=on:rtra=on_0");
   quick.push("dis+10_1:1_au=on:nm=2:plsq=on:plsqr=32,1:sos=all:i=20437:si=on:rtra=on_0");
   quick.push("dis+21_1:1_c=on:e2e=on:fe=axiom:sd=2:sp=frequency:ss=axioms:i=31036:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_cnfonf=conj_eager:fe=off:fsr=off:piset=and:prag=on:s2a=on:s2agt=40:sp=const_min:spb=non_intro:i=19675:si=on:rtra=on_0");
   quick.push("dis+2_1:3_au=on:bs=on:bsr=unit_only:e2e=on:hud=5:nwc=10.0:sgt=10:sos=on:sp=frequency:ss=axioms:i=22664:si=on:rtra=on_0");
   quick.push("lrs+10_1:1024_aac=none:anc=all:au=on:bd=off:fd=off:fe=off:kws=precedence:piset=pi_sigma:plsq=on:plsqr=4689123,65536:sos=all:sp=unary_frequency:i=7093:si=on:rtra=on_0");
   quick.push("ott+21_4:1_e2e=on:flr=on:nwc=10.0:s2a=on:s2at=3.0:i=32613:si=on:rtra=on_0");
   quick.push("lrs+1666_1:1_fe=axiom:prag=on:sos=all:sp=reverse_arity:ss=axioms:i=4712:si=on:rtra=on_0");
   quick.push("dis+21_1:1_fe=axiom:sd=1:sos=on:ss=axioms:i=6777:si=on:rtra=on_0");
   quick.push("dis+21_8:1_avsq=on:avsqr=1,16:cnfonf=off:fd=off:prag=on:s2a=on:slsq=on:slsqc=2:slsqr=2,31:sos=all:i=7099:si=on:rtra=on_0");
   quick.push("lrs+1002_4:1_afr=on:au=on:ins=2:kws=precedence:sos=on:sp=weighted_frequency:i=12621:si=on:rtra=on_0");
   quick.push("lrs+1010_4:1_avsq=on:sac=on:sp=const_max:ss=axioms:i=8888:si=on:rtra=on_0");
   quick.push("dis+10_5:4_acc=on:amm=off:cnfonf=off:ins=3:ixr=off:nwc=3.0:ss=axioms:st=2.0:i=8889:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_aac=none:au=on:cnfonf=lazy_not_gen_be_off:nm=16:ntd=on:nwc=5.0:s2a=on:s2at=4.5:i=8124:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_acc=on:au=on:avsq=on:bd=off:cnfonf=off:fe=off:sd=2:ss=axioms:st=2.0:i=8034:si=on:rtra=on_0");
   quick.push("lrs+21_3:1_au=on:avsq=on:avsqr=1,2:fsr=off:hfsq=on:nm=0:ntd=on:sd=1:ss=axioms:i=12690:si=on:rtra=on_0");
   quick.push("dis+2_1:40_au=on:av=off:fd=off:hfsq=on:hfsqr=1,32:nm=2:sos=on:sp=const_min:i=11391:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_au=on:cnfonf=off:fs=off:fsr=off:sd=10:sos=on:ss=axioms:st=5.0:i=8726:si=on:rtra=on_0");
   quick.push("ott+1010_2:1_abs=on:au=on:e2e=on:fde=unused:piset=equals:s2a=on:s2at=5.0:i=41200:si=on:rtra=on_0");
   quick.push("dis+21_1:1_avsq=on:avsqr=1,16:bd=off:hud=1:ins=1:prag=on:sos=on:ss=included:i=9461:si=on:rtra=on_0");
   quick.push("ott+10_16:1_bsd=on:c=on:nm=32:s2a=on:sac=on:sos=all:i=13341:si=on:rtra=on_0");
  // Improves by expected 21.49337275538251 probs costing 959748 Mi
  // Sub-schedule for 960000Mi strat cap / 960000Mi overall limit
   quick.push("ott-32_8:1_ntd=on:nwc=10.0:prag=on:sos=on:uhcvi=on:i=18524:si=on:rtra=on_0");
   quick.push("lrs+10_8:1_au=on:bet=on:c=on:cnfonf=off:lcm=reverse:piset=small_set:sd=1:sp=reverse_frequency:ss=axioms:i=90001:si=on:rtra=on_0");
   quick.push("lrs+1666_4:1_au=on:i=60219:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_anc=all:au=on:bd=off:cnfonf=off:fd=off:fs=off:fsr=off:nwc=5.0:sac=on:sos=on:ss=axioms:i=42160:si=on:rtra=on_0");
   quick.push("ott+1010_3:2_acc=on:au=on:cnfonf=off:fsr=off:ins=3:nm=40:ntd=on:s2a=on:s2agt=60:slsq=on:i=14357:si=on:rtra=on_0");
   quick.push("lrs+1002_1:3_apa=on:atotf=0.1:au=on:bd=off:cnfonf=off:plsq=on:plsqr=178679,1048576:sos=on:i=10665:si=on:rtra=on_0");
   quick.push("lrs+10_2:1_au=on:awrs=decay:bsr=on:e2e=on:fe=off:nm=40:nwc=10.0:piset=all:sos=all:i=9251:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:av=off:cnfonf=off:cs=on:fd=off:fde=unused:nm=4:ntd=on:prag=on:sos=all:sp=unary_first:i=9543:si=on:rtra=on_0");
   quick.push("lrs+1002_3:2_au=on:bsr=unit_only:hud=10:ntd=on:piset=all_but_not_eq:s2a=on:s2at=7.0:sd=2:sos=all:ss=axioms:i=16038:si=on:rtra=on_0");
   quick.push("lrs+10_8:3_bd=off:e2e=on:inj=on:s2agt=16:slsq=on:slsqc=1:ss=axioms:i=16221:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bd=off:fd=off:ntd=on:sos=on:i=111403:si=on:rtra=on_0");
   quick.push("dis+1010_2:3_abs=on:amm=off:atotf=0.4:au=on:avsq=on:fe=axiom:hfsq=on:hfsqc=1:kws=frequency:ntd=on:nwc=3.0:prag=on:s2a=on:i=6978:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_c=on:cnfonf=conj_eager:ins=3:nwc=4.0:plsq=on:plsqc=1:plsqr=15179,262144:sac=on:sd=1:ss=axioms:i=9037:si=on:rtra=on_0");
   quick.push("ott+10_3:1_c=on:cnfonf=lazy_not_be_gen:fsr=off:ntd=on:sd=10:sos=all:ss=axioms:st=2.0:i=9176:si=on:rtra=on_0");
   quick.push("lrs+1010_7:1_cnfonf=off:e2e=on:fe=off:hfaw=0:hflw=3:hfsq=on:hfsqc=3:ins=2:piset=or:spb=non_intro:i=25452:si=on:rtra=on_0");
   quick.push("dis+10_1:1_av=off:cnfonf=lazy_not_gen:fe=axiom:fsr=off:ins=3:nwc=10.0:s2a=on:i=35527:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cnfonf=off:e2e=on:hud=10:ins=2:plsq=on:plsqc=1:plsqr=32,1:s2a=on:sac=on:sos=on:i=26547:si=on:rtra=on_0");
   quick.push("ott+1010_8:1_atotf=0.2:au=on:bsr=unit_only:cha=on:e2e=on:fsr=off:sd=1:sp=unary_first:ss=axioms:st=4.0:i=14118:si=on:rtra=on_0");
   quick.push("ott+10_1:1_kws=arity:prag=on:sd=1:sos=all:ss=axioms:st=3.0:i=20084:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_au=on:cnfonf=lazy_gen:fsr=off:ntd=on:sp=const_min:tgt=full:i=29543:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_aac=none:au=on:cnfonf=off:inj=on:kws=precedence:ntd=on:sos=on:sp=reverse_arity:i=5501:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:cnfonf=off:e2e=on:sos=all:i=28740:si=on:rtra=on_0");
   quick.push("ott+4_1:1_cbe=off:cnfonf=lazy_not_be_gen:hud=20:irw=on:nwc=5.0:piset=all:plsq=on:plsqr=32,1:prag=on:sos=all:sp=occurrence:i=9860:si=on:rtra=on_0");
   quick.push("ott+10_1:8_fe=off:hfaw=5:hfsq=on:hfsqc=1:hfsqr=5,1:hud=15:nwc=15.0:prag=on:s2a=on:s2agt=16:ss=axioms:st=2.0:i=24782:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_av=off:e2e=on:nwc=13.0:s2a=on:ss=axioms:i=16679:si=on:rtra=on_0");
   quick.push("dis+10_16:1_acc=on:au=on:fd=off:fsr=off:hflw=0:hfsq=on:kws=precedence:sd=1:ss=axioms:st=1.5:i=15687:si=on:rtra=on_0");
   quick.push("lrs+10_4:1_hud=1:inj=on:prag=on:s2a=on:sos=all:i=16774:si=on:rtra=on_0");
   quick.push("ott+21_4:1_e2e=on:flr=on:nwc=10.0:s2a=on:s2at=3.0:i=32613:si=on:rtra=on_0");
   quick.push("dis+1002_5:1_au=on:cnfonf=lazy_pi_sigma_gen:fe=off:s2a=on:s2at=1.5:i=27060:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_au=on:bsr=unit_only:e2e=on:sos=on:ss=axioms:st=2.0:i=12207:si=on:rtra=on_0");
   quick.push("lrs+2_3:1_cnfonf=conj_eager:fe=axiom:ntd=on:sd=1:sgt=100:sp=occurrence:ss=axioms:i=13946:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_au=on:cbe=off:fe=off:nwc=10.0:sd=1:sos=on:ss=axioms:st=1.5:i=11320:si=on:rtra=on_0");
   quick.push("lrs+21_3:1_au=on:avsq=on:avsqr=1,2:fsr=off:hfsq=on:nm=0:ntd=on:sd=1:ss=axioms:i=12690:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_au=on:cnfonf=lazy_pi_sigma_gen:ntd=on:nwc=10.0:slsq=on:slsqc=1:sp=unary_frequency:uhcvi=on:i=32057:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:av=off:sd=2:sgt=64:sos=all:ss=axioms:i=115768:si=on:rtra=on_0");
  // Improves by expected 7.948723589584731 probs costing 950493 Mi
  // Sub-schedule for 960000Mi strat cap / 960000Mi overall limit
   quick.push("ott+1002_1:8_au=on:bd=off:cbe=off:e2e=on:fd=off:inj=on:nicw=on:sd=2:sos=on:sp=reverse_arity:ss=axioms:st=2.0:i=20258:si=on:rtra=on_0");
   quick.push("ott+10_8:1_apa=on:au=on:av=off:cnfonf=off:nwc=10.0:sp=reverse_arity:ss=axioms:i=50131:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_au=on:e2e=on:er=filter:hud=10:kws=precedence:sos=on:sp=weighted_frequency:ss=axioms:st=3.0:uhcvi=on:i=89296:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_au=on:bd=off:cnfonf=lazy_not_gen_be_off:kws=inv_frequency:ntd=on:nwc=15.0:plsq=on:plsqc=1:plsqr=6736429,1048576:i=25655:si=on:rtra=on_0");
   quick.push("lrs+1666_4:1_au=on:i=69997:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_au=on:cnfonf=lazy_gen:nwc=10.0:s2a=on:sp=unary_first:i=39214:si=on:rtra=on_0");
   quick.push("dis+10_8:1_au=on:avsq=on:avsqr=1,16:fe=off:fsr=off:plsq=on:plsqc=1:plsqr=32,1:rawr=on:i=68450:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:av=off:cnfonf=off:cs=on:fd=off:fde=unused:nm=4:ntd=on:prag=on:sos=all:sp=unary_first:i=11818:si=on:rtra=on_0");
   quick.push("dis+1010_2:3_abs=on:amm=off:atotf=0.4:au=on:avsq=on:fe=axiom:hfsq=on:hfsqc=1:kws=frequency:ntd=on:nwc=3.0:prag=on:s2a=on:i=26731:si=on:rtra=on_0");
   quick.push("ott+10_1:1_au=on:avsq=on:avsqr=1,16:c=on:cnfonf=off:sd=1:sos=all:ss=axioms:st=5.0:i=41921:si=on:rtra=on_0");
   quick.push("ott+1010_2:3_aac=none:afr=on:cnfonf=lazy_gen:fe=axiom:hud=1:nwc=10.0:piset=all_but_not_eq:prag=on:s2a=on:s2at=3.0:i=38728:si=on:rtra=on_0");
   quick.push("lrs+1010_5:1_au=on:cbe=off:s2a=on:s2agt=32:sac=on:i=153471:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:cnfonf=off:e2e=on:sos=all:i=28740:si=on:rtra=on_0");
   quick.push("lrs+10_4:1_hud=1:inj=on:prag=on:s2a=on:sos=all:i=16774:si=on:rtra=on_0");
   quick.push("ott+21_4:1_e2e=on:flr=on:nwc=10.0:s2a=on:s2at=3.0:i=32613:si=on:rtra=on_0");
   quick.push("lrs+10_1:16_hud=10:inj=on:nm=10:ntd=on:nwc=10.0:plsq=on:plsqr=1,32:s2a=on:s2at=3.0:sp=const_frequency:i=40581:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_au=on:cnfonf=lazy_gen:kws=inv_frequency:plsq=on:plsqc=1:plsqr=20,1:i=54328:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_au=on:cnfonf=off:fs=off:fsr=off:sd=10:sos=on:ss=axioms:st=5.0:i=114378:si=on:rtra=on_0");
  // Improves by expected 4.215704352839791 probs costing 923066 Mi
  // Overall score 874.3687486355826 probs on average / budget 3792674 Mi
    } else {
      // Sub-schedule for 10000Mi strat cap / 10000Mi overall limit
    quick.push("lrs+1002_1:1_au=on:av=off:fd=off:fde=unused:ntd=on:sos=on:sp=frequency:ss=axioms:i=782:si=on:rtra=on_0");
    quick.push("lrs+1002_2:3_avsq=on:fde=none:nwc=3.0:prag=on:sac=on:sd=2:sgt=32:sos=on:sp=unary_frequency:ss=axioms:i=754:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_au=on:cnfonf=off:e2e=on:piset=small_set:sac=on:sd=1:sos=all:ss=axioms:st=5.0:i=810:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_au=on:av=off:cnfonf=off:sd=1:sos=all:ss=axioms:st=1.5:i=617:si=on:rtra=on_0");
    quick.push("lrs+1010_1:1_e2e=on:ntd=on:nwc=5.0:sac=on:sd=1:sgt=16:spb=units:ss=axioms:i=660:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:bd=off:e2e=on:ins=3:sos=on:ss=axioms:i=707:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_e2e=on:fd=off:fe=off:prag=on:sos=on:i=826:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_au=on:e2e=on:fd=off:sos=on:sp=unary_frequency:ss=axioms:i=835:si=on:rtra=on_0");
    quick.push("dis+1010_3:1_acc=on:au=on:chr=on:cnfonf=off:fd=preordered:nwc=10.0:s2a=on:i=705:si=on:rtra=on_0");
    quick.push("dis+10_1:1_acc=on:avsq=on:e2e=on:ixr=off:s2a=on:sd=2:sp=occurrence:ss=axioms:i=608:si=on:rtra=on_0");
    quick.push("dis+10_1:1_au=on:e2e=on:fde=unused:nwc=5.0:sac=on:sos=all:sp=const_frequency:i=876:si=on:rtra=on_0");
    quick.push("lrs+1010_1:5_cnfonf=lazy_pi_sigma_gen:kws=precedence:nm=32:nwc=10.0:sp=const_frequency:i=15:si=on:rtra=on_0");
    quick.push("dis+1002_8:1_acc=model:au=on:avsq=on:fd=off:hfsq=on:s2a=on:s2agt=16:sgt=10:sp=unary_frequency:ss=axioms:i=1727:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:sd=1:ss=axioms:i=2:si=on:rtra=on_0");
    // Improves by expected 2258.269138383958 probs costing 9910 Mi
    // Sub-schedule for 20000Mi strat cap / 20000Mi overall limit
    quick.push("dis+1002_1:1_au=on:kws=inv_precedence:nwc=5.0:sd=1:sgt=32:ss=axioms:i=947:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_au=on:bd=off:cnfonf=off:fd=off:sos=all:i=2392:si=on:rtra=on_0");
    quick.push("lrs+1010_8:1_au=on:cnfonf=lazy_pi_sigma_gen:fde=none:nwc=10.0:s2a=on:sac=on:i=2494:si=on:rtra=on_0");
    quick.push("dis+10_3:1_acc=on:avsq=on:bs=unit_only:cnfonf=off:fe=axiom:ins=3:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=1258:si=on:rtra=on_0");
    quick.push("ott+2_1:128_bd=off:ins=3:kws=precedence:sd=1:sos=on:sp=frequency:ss=axioms:st=5.0:i=297:si=on:rtra=on_0");
    quick.push("lrs+0_1:1_fe=off:prag=on:sos=all:ss=axioms:i=988:si=on:rtra=on_0");
    quick.push("dis+10_1:1_au=on:cbe=off:nm=10:sd=1:sos=all:ss=axioms:st=3.0:i=423:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:kws=precedence:sos=on:sp=reverse_arity:ss=axioms:i=742:si=on:rtra=on_0");
    quick.push("lrs+1010_1:4_au=on:avsq=on:sd=2:sgt=8:ss=axioms:i=313:si=on:rtra=on_0");
    quick.push("lrs+1010_4:1_amm=off:awrs=decay:bsr=on:cbe=off:e2e=on:fde=none:fe=axiom:nwc=5.0:prag=on:sac=on:sd=1:spb=goal_then_units:ss=axioms:i=3335:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_hud=10:ins=2:sos=all:ss=axioms:tnu=1:i=229:si=on:rtra=on_0");
    quick.push("dis+10_8:1_au=on:e2e=on:sgt=8:ss=axioms:i=328:si=on:rtra=on_0");
    quick.push("ott+1002_1:1_bd=off:cbe=off:hud=1:prag=on:sos=on:sp=const_min:ss=axioms:i=649:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_au=on:e2e=on:fde=none:plsq=on:plsqc=1:plsqr=32,1:sos=on:sp=const_frequency:ss=axioms:st=3.0:i=1048:si=on:rtra=on_0");
    quick.push("ott+1002_17:12_au=on:ins=3:sac=on:sd=3:sos=on:sp=occurrence:ss=axioms:i=1918:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:fde=none:kws=inv_frequency:ntd=on:sos=on:i=942:si=on:rtra=on_0");
    quick.push("dis+1002_1:32_au=on:c=on:fd=off:nm=2:sd=1:sos=on:sp=frequency:ss=axioms:st=3.0:i=1354:si=on:rtra=on_0");
    quick.push("dis+10_1:1_s2a=on:s2agt=8:sd=2:sgt=8:ss=axioms:i=355:si=on:rtra=on_0");
    // Improves by expected 212.0573861120701 probs costing 19994 Mi
    // Sub-schedule for 30000Mi strat cap / 30000Mi overall limit
    quick.push("dis+10_4:1_avsq=on:e2e=on:fde=none:s2a=on:s2at=3.0:slsq=on:slsqc=1:i=1101:si=on:rtra=on_0");
    quick.push("dis+10_1:1_avsq=on:cs=on:e2e=on:i=290:si=on:rtra=on_0");
    quick.push("ott+1010_3:1_bd=preordered:cbe=off:e2e=on:fe=axiom:hud=5:s2a=on:s2agt=60:slsq=on:ss=axioms:tnu=1:i=2233:si=on:rtra=on_0");
    quick.push("dis+10_1:1_avsq=on:cnfonf=lazy_pi_sigma_gen:sd=1:ss=axioms:i=265:si=on:rtra=on_0");
    quick.push("lrs+2_1:64_bd=off:nwc=5.0:sd=2:ss=axioms:i=290:si=on:rtra=on_0");
    quick.push("lrs+1002_2:3_avsq=on:fde=none:nwc=3.0:prag=on:sac=on:sd=2:sgt=32:sos=on:sp=unary_frequency:ss=axioms:i=3711:si=on:rtra=on_0");
    quick.push("lrs+1002_1:128_bd=off:e2e=on:ins=1:sac=on:sd=1:sos=on:ss=axioms:st=2.0:i=585:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_apa=on:au=on:cnfonf=off:e2e=on:hud=15:sos=on:i=1337:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_au=on:av=off:cnfonf=off:sd=1:sos=all:ss=axioms:st=1.5:i=1186:si=on:rtra=on_0");
    quick.push("lrs+4_1:1_fd=off:fs=off:fsr=off:sac=on:sos=on:ss=axioms:i=413:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_e2e=on:nwc=5.0:sd=1:sgt=30:ss=axioms:i=980:si=on:rtra=on_0");
    quick.push("dis+10_3:1_avsq=on:sd=1:ss=axioms:st=2.0:tgt=ground:i=278:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_kws=precedence:sos=on:sp=frequency:ss=axioms:i=252:si=on:rtra=on_0");
    quick.push("lrs+31_1:1_au=on:cnfonf=off:ins=3:plsq=on:sd=1:sgt=32:sos=on:ss=axioms:i=494:si=on:rtra=on_0");
    quick.push("lrs+10_1:128_fd=off:hud=20:sos=on:ss=axioms:tnu=2:i=289:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_bsd=on:fsd=on:nwc=10.0:sd=1:ss=axioms:i=401:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_sd=1:sgt=30:sp=reverse_arity:ss=axioms:tgt=full:i=633:si=on:rtra=on_0");
    quick.push("dis+10_1:1_acc=on:avsq=on:avsqr=1,16:kws=arity_squared:nm=20:sd=1:sp=const_frequency:ss=axioms:i=134:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_er=filter:fd=off:flr=on:nwc=10.0:ss=axioms:st=3.0:i=365:si=on:rtra=on_0");
    quick.push("lrs+20_1:1_au=on:bd=off:erd=off:fde=none:sos=on:i=493:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_bd=off:fde=unused:fe=off:fs=off:fsr=off:hud=10:sos=on:i=719:si=on:rtra=on_0");
    quick.push("dis+10_1:1_hud=5:nm=16:prag=on:sac=on:sos=on:ss=axioms:tnu=2:i=1029:si=on:rtra=on_0");
    quick.push("dis+21_1:1_au=on:c=on:cnfonf=off:e2e=on:ins=1:kws=precedence:ntd=on:sd=2:sos=on:ss=axioms:st=2.0:i=640:si=on:rtra=on_0");
    quick.push("dis+10_1:32_fd=off:kws=precedence:sd=2:sos=on:ss=axioms:i=237:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_sd=2:slsq=on:slsqc=1:ss=axioms:i=751:si=on:rtra=on_0");
    quick.push("ott+10_1:1_atotf=0.1:au=on:cnfonf=off:e2e=on:fsr=off:ins=4:kws=precedence:s2a=on:i=2166:si=on:rtra=on_0");
    quick.push("lrs+1002_1:2_e2e=on:sd=2:sgt=16:ss=axioms:i=502:si=on:rtra=on_0");
    quick.push("dis+1002_8:1_acc=model:au=on:avsq=on:fd=off:hfsq=on:s2a=on:s2agt=16:sgt=10:sp=unary_frequency:ss=axioms:i=4453:si=on:rtra=on_0");
    quick.push("dis+10_4:1_apa=on:au=on:cnfonf=off:fde=none:sd=2:ss=axioms:st=3.0:i=691:si=on:rtra=on_0");
    quick.push("lrs+10_1:4_au=on:av=off:bd=off:e2e=on:sos=all:i=1786:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_e2e=on:hud=10:sd=1:ss=axioms:st=3.0:tgt=ground:i=621:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_au=on:fd=preordered:sos=on:ss=axioms:st=1.5:i=621:si=on:rtra=on_0");
    // Improves by expected 134.93277978747452 probs costing 29914 Mi
    // Sub-schedule for 60000Mi strat cap / 60000Mi overall limit
    quick.push("lrs+10_1:1_au=on:cnfonf=off:sd=1:sos=all:ss=axioms:st=3.0:i=541:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:av=off:fd=off:fde=unused:ntd=on:sos=on:sp=frequency:ss=axioms:i=2132:si=on:rtra=on_0");
    quick.push("dis+2_16:1_e2e=on:gs=on:s2a=on:s2agt=32:sgt=32:ss=axioms:i=1182:si=on:rtra=on_0");
    quick.push("dis+1010_1:1_au=on:c=on:ins=3:plsq=on:plsqc=5:sd=1:sos=on:ss=axioms:i=567:si=on:rtra=on_0");
    quick.push("ott+10_5:4_au=on:avsq=on:bs=unit_only:bsr=unit_only:fsr=off:ins=3:kws=arity:sd=1:sos=all:ss=axioms:i=1467:si=on:rtra=on_0");
    quick.push("dis+10_1:1_au=on:avsq=on:avsqr=16,1:fd=off:nm=2:sos=all:i=890:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_aac=none:au=on:fde=unused:nm=2:sac=on:sos=all:i=5985:si=on:rtra=on_0");
    quick.push("dis+1010_1:1_apa=on:bsr=on:cnfonf=off:hud=10:ins=2:kws=inv_frequency:sd=2:slsq=on:slsqc=5:sos=on:ss=axioms:i=240:si=on:rtra=on_0");
    quick.push("lrs+10_8:1_bd=off:fd=off:kws=inv_precedence:sos=on:ss=axioms:i=375:si=on:rtra=on_0");
    quick.push("ott+10_1:1_acc=model:avsq=on:c=on:cnfonf=off:fd=off:nm=0:sp=reverse_arity:ss=axioms:i=551:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_afp=1010:fde=unused:fe=off:hud=10:kws=arity_squared:prag=on:sos=on:sp=reverse_arity:i=1031:si=on:rtra=on_0");
    quick.push("dis+1002_2:3_aac=none:au=on:avsq=on:cbe=off:fde=none:lcm=predicate:nm=32:prag=on:sos=on:sp=unary_first:ss=axioms:st=2.0:i=1600:si=on:rtra=on_0");
    quick.push("dis+10_5:1_au=on:avsq=on:ss=axioms:i=516:si=on:rtra=on_0");
    quick.push("lrs+1010_1:1_e2e=on:ntd=on:nwc=5.0:sac=on:sd=1:sgt=16:spb=units:ss=axioms:i=3945:si=on:rtra=on_0");
    quick.push("lrs+1010_1:128_au=on:cnfonf=conj_eager:ins=1:sac=on:sp=const_max:ss=axioms:st=3.0:tgt=ground:i=267:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_au=on:e2e=on:hud=10:sd=4:sos=on:ss=axioms:st=2.0:i=828:si=on:rtra=on_0");
    quick.push("ott+1010_1:4_au=on:avsq=on:avsqc=1:cnfonf=off:e2e=on:fsr=off:ins=1:nwc=10.0:s2a=on:s2at=2.5:sac=on:sp=const_min:i=693:si=on:rtra=on_0");
    quick.push("lrs+1010_1:4_au=on:e2e=on:hud=10:nm=32:plsq=on:plsqc=1:plsqr=32,1:sac=on:sos=on:i=1381:si=on:rtra=on_0");
    quick.push("dis+10_1:64_cnfonf=lazy_not_be_gen:cond=fast:fsr=off:hud=5:ntd=on:nwc=10.0:sac=on:sd=1:sos=on:sp=const_max:ss=axioms:i=798:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_au=on:e2e=on:fd=off:sos=on:sp=unary_frequency:ss=axioms:i=3962:si=on:rtra=on_0");
    quick.push("lrs+2_1:3_au=on:bd=off:e2e=on:sos=on:ss=axioms:i=577:si=on:rtra=on_0");
    quick.push("dis+1010_8:1_au=on:avsq=on:cbe=off:plsq=on:plsqc=1:plsqr=32,1:rawr=on:rp=on:sd=2:ss=axioms:st=3.0:i=5743:si=on:rtra=on_0");
    quick.push("dis+10_5:1_cnfonf=off:slsq=on:sp=const_max:i=571:si=on:rtra=on_0");
    quick.push("dis+10_1:1_e2e=on:hflw=5:hfsq=on:hfsqc=8:hfsql=off:i=273:si=on:rtra=on_0");
    quick.push("lrs+0_1:1_au=on:ins=3:kws=precedence:ntd=on:sos=on:sp=const_max:ss=axioms:i=476:si=on:rtra=on_0");
    quick.push("dis+2_1:1_cnfonf=off:e2e=on:kws=inv_frequency:nm=0:nwc=5.0:s2a=on:s2agt=32:ss=axioms:i=487:si=on:rtra=on_0");
    quick.push("ott+1010_8:1_e2e=on:plsq=on:plsqr=32,1:sgt=8:ss=axioms:i=1796:si=on:rtra=on_0");
    quick.push("dis+22_1:1_au=on:fe=axiom:ntd=on:nwc=10.0:s2a=on:i=559:si=on:rtra=on_0");
    quick.push("dis+10_1:1_acc=on:avsq=on:avsqr=1,16:kws=arity_squared:nm=20:sd=1:sp=const_frequency:ss=axioms:i=638:si=on:rtra=on_0");
    quick.push("lrs+1010_16:1_acc=on:anc=all_dependent:avsq=on:fde=unused:hud=1:ins=2:piset=all_but_not_eq:prag=on:sac=on:i=6474:si=on:rtra=on_0");
    quick.push("lrs+10_5:1_cnfonf=lazy_not_gen_be_off:hud=5:sd=1:ss=axioms:i=597:si=on:rtra=on_0");
    quick.push("ott+2_1:128_bd=off:ins=3:kws=precedence:sd=1:sos=on:sp=frequency:ss=axioms:st=5.0:i=290:si=on:rtra=on_0");
    quick.push("dis+2_1:1_au=on:avsq=on:nm=0:sd=1:ss=axioms:i=708:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_avsq=on:fsr=off:nm=2:prag=on:sos=on:i=748:si=on:rtra=on_0");
    quick.push("dis+1010_1:16_amm=sco:cnfonf=off:sd=1:ss=axioms:st=2.0:tgt=full:tnu=5:i=1806:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_bd=preordered:hud=15:kws=precedence:nm=16:sd=3:sgt=16:sos=on:sp=frequency:ss=axioms:i=483:si=on:rtra=on_0");
    quick.push("ott+10_16:1_aac=none:au=on:cnfonf=off:nm=20:s2a=on:ss=axioms:i=5155:si=on:rtra=on_0");
    quick.push("dis+1010_1:1_au=on:cnfonf=lazy_pi_sigma_gen:fd=off:fsr=off:s2a=on:s2agt=10:i=1398:si=on:rtra=on_0");
    quick.push("dis+32_1:2_au=on:cnfonf=lazy_pi_sigma_gen:kws=inv_precedence:nwc=10.0:s2a=on:s2agt=30:i=1441:si=on:rtra=on_0");
    quick.push("dis+10_1:8_ins=1:nm=6:s2a=on:sd=3:ss=axioms:i=451:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:ins=2:sos=on:ss=axioms:st=1.5:i=350:si=on:rtra=on_0");
    // Improves by expected 120.32336523397528 probs costing 59931 Mi
    // Sub-schedule for 120000Mi strat cap / 120000Mi overall limit
    quick.push("lrs+10_1:1_au=on:av=off:cnfonf=off:fde=none:fsr=off:sos=on:sp=const_frequency:i=854:si=on:rtra=on_0");
    quick.push("dis+10_1:1_acc=on:fde=none:kws=inv_precedence:nwc=5.0:plsq=on:plsqc=1:plsqr=6,1:prag=on:s2a=on:i=1328:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_cs=on:prag=on:sos=on:i=1475:si=on:rtra=on_0");
    quick.push("ott+10_1:1_hud=15:ins=1:sd=1:sgt=32:sos=all:ss=axioms:st=2.0:i=1132:si=on:rtra=on_0");
    quick.push("ott+1010_1:1_au=on:av=off:cnfonf=lazy_not_gen_be_off:fe=axiom:kws=arity:nwc=5.0:ss=axioms:i=4969:si=on:rtra=on_0");
    quick.push("lrs+10_8:1_cbe=off:e2e=on:hud=10:sd=1:ss=axioms:st=3.0:tgt=ground:i=1144:si=on:rtra=on_0");
    quick.push("lrs+10_4:1_au=on:avsq=on:e2e=on:fde=unused:nm=6:nwc=10.0:sac=on:i=4810:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_atotf=0.1:au=on:cnfonf=off:inj=on:piset=and:s2a=on:sos=on:i=944:si=on:rtra=on_0");
    quick.push("dis-1010_1:1_au=on:avsq=on:e2e=on:nm=0:s2a=on:s2at=1.5:i=2837:si=on:rtra=on_0");
    quick.push("dis+1010_1:1_apa=on:bsr=on:cnfonf=off:hud=10:ins=2:kws=inv_frequency:sd=2:slsq=on:slsqc=5:sos=on:ss=axioms:i=240:si=on:rtra=on_0");
    quick.push("lrs+1010_1:1_bd=off:cnfonf=off:hud=10:nm=32:sac=on:sd=1:sims=off:sos=all:ss=axioms:st=2.0:i=1511:si=on:rtra=on_0");
    quick.push("dis-1004_8:1_av=off:bd=off:fd=off:fe=off:hud=22:sos=on:tnu=2:i=883:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_au=on:av=off:fde=unused:hfsq=on:hfsqr=16,1:hud=10:lma=on:nm=3:piset=and:sos=all:sp=const_frequency:i=408:si=on:rtra=on_0");
    quick.push("dis+1002_1:2_cnfonf=lazy_pi_sigma_gen:ins=1:nm=32:ntd=on:nwc=10.0:prag=on:s2at=3.0:slsq=on:slsqr=1,16:i=1080:si=on:rtra=on_0");
    quick.push("dis+1010_4:1_amm=off:bs=on:c=on:cbe=off:nm=64:nwc=6.0:s2a=on:s2at=5.0:sac=on:slsq=on:slsqr=1,8:i=1108:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_ins=3:prag=on:sos=on:sp=const_min:i=907:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_au=on:cnfonf=off:e2e=on:piset=small_set:sac=on:sd=1:sos=all:ss=axioms:st=5.0:i=1025:si=on:rtra=on_0");
    quick.push("ott+1010_1:128_afp=1010:afq=2.19963:avsq=on:avsqr=1,8:er=known:sd=1:ss=axioms:i=1045:si=on:rtra=on_0");
    quick.push("lrs+1010_1:128_au=on:cnfonf=conj_eager:ins=1:sac=on:sp=const_max:ss=axioms:st=3.0:tgt=ground:i=241:si=on:rtra=on_0");
    quick.push("lrs+10_1:128_au=on:av=off:cnfonf=off:cond=fast:nm=6:sos=all:i=2216:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_av=off:bd=off:fd=off:kws=inv_frequency:sos=on:i=766:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_au=on:kws=inv_precedence:nwc=5.0:sd=1:sgt=32:ss=axioms:i=3722:si=on:rtra=on_0");
    quick.push("lrs+1010_16:1_apa=on:au=on:bsr=on:cnfonf=off:fe=off:nm=32:prag=on:sac=on:sos=on:sp=unary_first:ss=axioms:i=1895:si=on:rtra=on_0");
    quick.push("dis+10_1:1_atotf=0.5:fe=axiom:fsr=off:sd=1:sgt=16:sos=all:ss=axioms:i=1467:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_au=on:e2e=on:fd=off:sos=on:sp=unary_frequency:ss=axioms:i=464:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_bd=off:e2e=on:fe=off:prag=on:sos=all:sp=const_frequency:ss=axioms:i=4945:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_bd=off:e2e=on:ins=2:sd=1:sos=all:ss=axioms:st=3.0:i=326:si=on:rtra=on_0");
    quick.push("ott+10_4:1_e2e=on:fde=unused:nm=40:nwc=10.0:s2a=on:s2at=2.0:sp=unary_frequency:ss=axioms:i=1443:si=on:rtra=on_0");
    quick.push("lrs+2_1:6_au=on:cnfonf=off:ss=axioms:st=1.5:i=1438:si=on:rtra=on_0");
    quick.push("dis+21_8:1_au=on:cbe=off:cnfonf=off:hud=15:nwc=5.0:piset=not:sos=all:sp=unary_frequency:ss=axioms:i=3365:si=on:rtra=on_0");
    quick.push("dis+10_1:128_av=off:fde=unused:hud=1:prag=on:sos=all:ss=axioms:i=3425:si=on:rtra=on_0");
    quick.push("dis+3_7:4_bsr=on:c=on:erd=off:fde=none:hud=10:lma=on:nwc=5.0:sac=on:sos=on:sp=frequency:i=2203:si=on:rtra=on_0");
    quick.push("lrs+31_1:1_au=on:cnfonf=off:ins=3:plsq=on:sd=1:sgt=32:sos=on:ss=axioms:i=289:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_aac=none:cbe=off:cnfonf=lazy_pi_sigma_gen:sos=all:sp=const_max:uhcvi=on:i=753:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_avsq=on:bsd=on:cnfonf=off:nm=10:piset=all_but_not_eq:s2a=on:s2at=6.0:sp=const_min:i=2214:si=on:rtra=on_0");
    quick.push("ott+2_1:1024_apa=on:atotf=0.2:bd=off:cnfonf=off:erd=off:fd=off:nm=0:sos=all:i=1527:si=on:rtra=on_0");
    quick.push("lrs+10_1:128_bd=off:chr=on:erd=off:fd=off:fe=axiom:hud=10:sac=on:sos=on:i=538:si=on:rtra=on_0");
    quick.push("lrs+1010_8:1_c=on:fsr=off:hud=0:kws=inv_arity:ntd=on:sos=on:sp=occurrence:i=1098:si=on:rtra=on_0");
    quick.push("dis+22_1:1_au=on:fe=axiom:ntd=on:nwc=10.0:s2a=on:i=1348:si=on:rtra=on_0");
    quick.push("ott+10_1:1_s2a=on:s2at=2.0:sd=2:ss=axioms:i=7135:si=on:rtra=on_0");
    quick.push("dis+21_1:4_avsq=on:avsqr=924271,1048576:c=on:e2e=on:fs=off:fsr=off:piset=and:plsq=on:plsqr=32,1:sd=10:sos=on:sp=unary_first:ss=axioms:st=1.5:tnu=2:i=791:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_e2e=on:sd=1:ss=axioms:st=3.0:i=6037:si=on:rtra=on_0");
    quick.push("dis+1010_3:1_acc=on:au=on:chr=on:cnfonf=off:fd=preordered:nwc=10.0:s2a=on:i=938:si=on:rtra=on_0");
    quick.push("dis+10_1:1_acc=on:avsq=on:e2e=on:ixr=off:s2a=on:sd=2:sp=occurrence:ss=axioms:i=4357:si=on:rtra=on_0");
    quick.push("dis+10_1:2_au=on:cnfonf=lazy_pi_sigma_gen:ss=axioms:st=1.2:tgt=ground:i=938:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_bs=on:e2e=on:prag=on:sos=on:ss=axioms:i=2052:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:bd=off:kws=precedence:sos=on:sp=frequency:ss=axioms:st=3.0:i=728:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_au=on:cnfonf=lazy_pi_sigma_gen:sd=1:slsq=on:ss=axioms:i=753:si=on:rtra=on_0");
    quick.push("lrs+1002_4:1_au=on:cnfonf=off:er=filter:fde=none:ntd=on:nwc=10.0:i=1213:si=on:rtra=on_0");
    quick.push("dis+21_1:1_au=on:c=on:cnfonf=off:e2e=on:ins=1:kws=precedence:ntd=on:sd=2:sos=on:ss=axioms:st=2.0:i=1417:si=on:rtra=on_0");
    quick.push("ott+2_4:1_au=on:cnfonf=lazy_pi_sigma_gen:hud=16:ins=3:nm=20:plsq=on:plsqc=1:plsqr=13,2:rawr=on:sp=reverse_arity:ss=axioms:st=3.0:i=2643:si=on:rtra=on_0");
    quick.push("lrs+21_1:128_acc=model:au=on:cbe=off:e2e=on:pe=on:piset=small_set:sos=on:sp=occurrence:ss=axioms:i=1179:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_e2e=on:prag=on:rawr=on:sos=on:sp=weighted_frequency:i=991:si=on:rtra=on_0");
    quick.push("dis+21_1:1_bd=off:e2e=on:s2a=on:s2agt=32:sfv=off:ss=axioms:st=2.0:i=1247:si=on:rtra=on_0");
    quick.push("ott+10_4:1_au=on:cnfonf=lazy_gen:fde=unused:kws=precedence:s2a=on:s2at=2.0:sd=1:ss=axioms:st=5.0:i=2161:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_au=on:fde=none:sos=all:i=1840:si=on:rtra=on_0");
    quick.push("dis+1010_1:20_au=on:av=off:cbe=off:fe=off:nm=2:sos=on:sp=weighted_frequency:uhcvi=on:i=1141:si=on:rtra=on_0");
    quick.push("dis+10_1:8_au=on:c=on:sos=all:ss=axioms:i=1777:si=on:rtra=on_0");
    quick.push("dis+10_1:5_cnfonf=off:e2e=on:fsr=off:prag=on:s2a=on:i=647:si=on:rtra=on_0");
    quick.push("dis+10_1:128_atotf=0.1:fd=off:fsr=off:hflw=5:hfsq=on:hfsqc=5:hfsql=off:hfsqr=1,16:plsq=on:plsqr=9,8:tnu=1:i=1197:si=on:rtra=on_0");
    quick.push("ott+1666_4:1_au=on:bd=off:erd=off:ntd=on:sos=all:i=1038:si=on:rtra=on_0");
    quick.push("dis+21_1:1_au=on:e2e=on:hfsq=on:hfsql=off:lcm=reverse:nm=32:nwc=10.0:s2a=on:s2at=3.0:sd=1:ss=axioms:st=6.0:i=1290:si=on:rtra=on_0");
    quick.push("dis-1010_1:1_acc=on:au=on:bd=off:sgt=16:ss=axioms:tgt=full:i=6550:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:cnfonf=off:sos=on:ss=axioms:i=4664:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_afr=on:cs=on:e2e=on:hfsq=on:hfsqc=20:ntd=on:nwc=10.0:s2a=on:i=1215:si=on:rtra=on_0");
    quick.push("dis+10_1:1024_bd=preordered:fde=unused:prag=on:sos=on:i=743:si=on:rtra=on_0");
    // Improves by expected 102.61049630834741 probs costing 119999 Mi
    // Sub-schedule for 240000Mi strat cap / 240000Mi overall limit
    quick.push("dis+10_4:1_avsq=on:e2e=on:fde=none:s2a=on:s2at=3.0:slsq=on:slsqc=1:i=1101:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_au=on:cnfonf=off:sd=1:sos=all:ss=axioms:st=3.0:i=972:si=on:rtra=on_0");
    quick.push("dis+10_1:1_acc=on:fde=none:kws=inv_precedence:nwc=5.0:plsq=on:plsqc=1:plsqr=6,1:prag=on:s2a=on:i=4577:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_au=on:bsd=on:ins=3:plsq=on:plsqc=1:plsqr=1,1:s2a=on:s2at=3.0:sd=10:sp=weighted_frequency:ss=axioms:i=1655:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:av=off:fd=off:fde=unused:ntd=on:sos=on:sp=frequency:ss=axioms:i=2115:si=on:rtra=on_0");
    quick.push("ott+1010_3:1_bd=preordered:cbe=off:e2e=on:fe=axiom:hud=5:s2a=on:s2agt=60:slsq=on:ss=axioms:tnu=1:i=7155:si=on:rtra=on_0");
    quick.push("dis+1010_8:1_cnfonf=lazy_gen:fe=off:fsr=off:hud=15:nwc=10.0:s2a=on:i=4273:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_fe=off:hud=10:sos=on:ss=axioms:i=1016:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:e2e=on:fde=none:ins=3:kws=precedence:s2a=on:s2at=5.0:sp=frequency:i=2335:si=on:rtra=on_0");
    quick.push("lrs+1010_1:1_au=on:av=off:bsd=on:cnfonf=off:kws=arity_squared:sp=const_min:ss=axioms:i=3375:si=on:rtra=on_0");
    quick.push("ott+10_5:4_au=on:avsq=on:bs=unit_only:bsr=unit_only:fsr=off:ins=3:kws=arity:sd=1:sos=all:ss=axioms:i=5339:si=on:rtra=on_0");
    quick.push("dis+10_1:1_au=on:avsq=on:avsqr=16,1:fd=off:nm=2:sos=all:i=5800:si=on:rtra=on_0");
    quick.push("dis+21_2:3_cnfonf=conj_eager:fsr=off:sd=1:slsq=on:ss=axioms:st=4.0:i=1845:si=on:rtra=on_0");
    quick.push("lrs+1002_2:3_avsq=on:fde=none:nwc=3.0:prag=on:sac=on:sd=2:sgt=32:sos=on:sp=unary_frequency:ss=axioms:i=6172:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_au=on:av=off:fde=unused:hfsq=on:hfsqr=16,1:hud=10:lma=on:nm=3:piset=and:sos=all:sp=const_frequency:i=9434:si=on:rtra=on_0");
    quick.push("ott+1010_16:1_av=off:fe=off:hud=10:ins=5:nwc=3.0:prag=on:rawr=on:i=4927:si=on:rtra=on_0");
    quick.push("dis+2_1:1_hflw=5:hfsq=on:hfsqc=8:hfsql=off:hfsqr=1,2:piset=pi_sigma:spb=goal:i=1805:si=on:rtra=on_0");
    quick.push("ott+1010_1:1_au=on:bd=off:e2e=on:fde=none:ins=1:prag=on:sos=on:i=6247:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_au=on:avsq=on:hud=22:ins=3:ntd=on:nwc=3.0:s2a=on:sp=weighted_frequency:i=2589:si=on:rtra=on_0");
    quick.push("lrs+1010_1:128_au=on:cnfonf=conj_eager:ins=1:sac=on:sp=const_max:ss=axioms:st=3.0:tgt=ground:i=241:si=on:rtra=on_0");
    quick.push("lrs+1010_3:1_au=on:bd=off:fde=none:lecc=1.5:nwc=10.0:i=9473:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_e2e=on:fd=off:fe=off:prag=on:sos=on:i=4492:si=on:rtra=on_0");
    quick.push("dis+10_1:64_cnfonf=lazy_not_be_gen:cond=fast:fsr=off:hud=5:ntd=on:nwc=10.0:sac=on:sd=1:sos=on:sp=const_max:ss=axioms:i=798:si=on:rtra=on_0");
    quick.push("dis+10_16:1_au=on:avsq=on:cnfonf=conj_eager:piset=equals:s2a=on:sp=occurrence:ss=axioms:i=3218:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_au=on:e2e=on:fd=off:sos=on:sp=unary_frequency:ss=axioms:i=464:si=on:rtra=on_0");
    quick.push("lrs+2_1:3_au=on:bd=off:e2e=on:sos=on:ss=axioms:i=2601:si=on:rtra=on_0");
    quick.push("ott+10_4:1_e2e=on:fde=unused:nm=40:nwc=10.0:s2a=on:s2at=2.0:sp=unary_frequency:ss=axioms:i=11317:si=on:rtra=on_0");
    quick.push("dis+10_16:1_au=on:avsq=on:c=on:chr=on:nm=2:sac=on:sp=unary_first:ss=axioms:i=2545:si=on:rtra=on_0");
    quick.push("lrs+10_2:1_fde=none:prag=on:sd=2:sgt=8:ss=axioms:tgt=ground:i=11785:si=on:rtra=on_0");
    quick.push("lrs+1010_8:1_au=on:cnfonf=lazy_pi_sigma_gen:fde=none:nwc=10.0:s2a=on:sac=on:i=4513:si=on:rtra=on_0");
    quick.push("lrs+1010_4:1_acc=on:au=on:bd=off:sfv=off:ss=axioms:i=10881:si=on:rtra=on_0");
    quick.push("lrs+10_5:1_avsq=on:avsqr=16,1:cnfonf=conj_eager:nwc=10.0:plsq=on:plsqc=1:plsqr=32,1:sd=2:spb=intro:ss=axioms:i=1928:si=on:rtra=on_0");
    quick.push("lrs+10_1:128_fd=off:hud=20:sos=on:ss=axioms:tnu=2:i=1063:si=on:rtra=on_0");
    quick.push("lrs+1010_1:128_au=on:avsq=on:fsr=off:ins=3:kws=frequency:sos=all:i=1479:si=on:rtra=on_0");
    quick.push("lrs+10_1:128_bd=off:chr=on:erd=off:fd=off:fe=axiom:hud=10:sac=on:sos=on:i=538:si=on:rtra=on_0");
    quick.push("lrs+21_8:1_cnfonf=lazy_not_gen:nm=2:nwc=10.0:plsq=on:plsqc=2:plsqr=6,1:prag=on:sgt=8:sp=unary_frequency:ss=axioms:i=10373:si=on:rtra=on_0");
    quick.push("ott+1010_1:1_cnfonf=off:fd=off:rp=on:sac=on:sos=on:i=1264:si=on:rtra=on_0");
    quick.push("dis+10_16:1_au=on:avsq=on:bet=on:cbe=off:cnfonf=off:ins=3:ntd=on:plsq=on:plsqc=1:plsqr=32,1:i=3847:si=on:rtra=on_0");
    quick.push("dis+1002_1:2_au=on:bs=on:bsr=unit_only:c=on:fsr=off:hud=10:kws=inv_precedence:nm=6:ntd=on:nwc=10.0:sac=on:sos=on:i=1617:si=on:rtra=on_0");
    quick.push("dis+10_1:12_cnfonf=conj_eager:ss=axioms:st=3.0:tgt=full:i=620:si=on:rtra=on_0");
    quick.push("lrs+1666_1:1_bd=off:bet=on:bsd=on:bsr=unit_only:fde=none:nwc=10.0:sp=occurrence:i=2482:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_atotf=0.2:au=on:bd=off:cnfonf=off:e2e=on:sos=all:i=3365:si=on:rtra=on_0");
    quick.push("dis+10_1:1_cnfonf=off:fde=none:ss=axioms:i=1579:si=on:rtra=on_0");
    quick.push("dis+10_1:1_acc=on:avsq=on:e2e=on:ixr=off:s2a=on:sd=2:sp=occurrence:ss=axioms:i=490:si=on:rtra=on_0");
    quick.push("dis+10_3:1_acc=on:avsq=on:bs=unit_only:cnfonf=off:fe=axiom:ins=3:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=7308:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_er=filter:fd=off:flr=on:nwc=10.0:ss=axioms:st=3.0:i=365:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_au=on:cnfonf=off:sd=1:sgt=16:sp=occurrence:ss=axioms:i=1367:si=on:rtra=on_0");
    quick.push("lrs+20_1:1_au=on:bd=off:erd=off:fde=none:sos=on:i=3577:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_aac=none:c=on:cnfonf=lazy_not_gen:sos=on:i=3633:si=on:rtra=on_0");
    quick.push("dis+1004_1:5_avsq=on:cs=on:e2e=on:ins=2:sos=all:i=1188:si=on:rtra=on_0");
    quick.push("dis+10_1:1_cnfonf=off:fe=off:nwc=10.0:s2a=on:s2agt=8:sd=1:ss=axioms:st=5.0:i=357:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:bd=off:kws=precedence:sos=on:sp=frequency:ss=axioms:st=3.0:i=728:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_au=on:cnfonf=lazy_pi_sigma_gen:sd=1:slsq=on:ss=axioms:i=568:si=on:rtra=on_0");
    quick.push("dis+21_1:1_au=on:c=on:cnfonf=off:e2e=on:ins=1:kws=precedence:ntd=on:sd=2:sos=on:ss=axioms:st=2.0:i=5301:si=on:rtra=on_0");
    quick.push("dis+1010_73:128_bd=preordered:fsr=off:nwc=3.0:s2a=on:s2at=2.0:i=909:si=on:rtra=on_0");
    quick.push("lrs+10_5:1_av=off:cnfonf=lazy_pi_sigma_gen:nwc=5.0:prag=on:s2a=on:s2agt=16:i=3801:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_bd=preordered:hud=15:kws=precedence:nm=16:sd=3:sgt=16:sos=on:sp=frequency:ss=axioms:i=668:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_aac=none:bd=off:ins=2:sos=on:sp=reverse_frequency:ss=axioms:i=559:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:c=on:cnfonf=off:kws=inv_precedence:piset=and:sd=1:ss=axioms:tgt=ground:tnu=2:i=9010:si=on:rtra=on_0");
    quick.push("lrs+10_97:429_c=on:cnfonf=lazy_gen:fe=axiom:ntd=on:s2a=on:sp=const_frequency:tgt=ground:i=1342:si=on:rtra=on_0");
    quick.push("lrs+21_1:128_acc=model:au=on:cbe=off:e2e=on:pe=on:piset=small_set:sos=on:sp=occurrence:ss=axioms:i=494:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_bd=off:bs=unit_only:bsd=on:cnfonf=off:fde=unused:fsr=off:hud=5:kws=inv_arity_squared:sp=const_min:i=2235:si=on:rtra=on_0");
    quick.push("dis+10_8:1_au=on:nwc=10.0:sos=all:i=3282:si=on:rtra=on_0");
    quick.push("lrs-4_1:1_sd=1:sgt=8:sos=all:ss=axioms:i=882:si=on:rtra=on_0");
    quick.push("dis+1002_8:1_acc=model:au=on:avsq=on:fd=off:hfsq=on:s2a=on:s2agt=16:sgt=10:sp=unary_frequency:ss=axioms:i=5939:si=on:rtra=on_0");
    quick.push("ott+10_1:64_aac=none:acc=on:au=on:avsq=on:avsqr=2,15:cnfonf=lazy_not_gen_be_off:ins=1:tgt=full:i=3310:si=on:rtra=on_0");
    quick.push("ott+10_2:1_au=on:cnfonf=off:ins=1:plsq=on:plsqc=1:plsqr=10813507,131072:i=6244:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_au=on:e2e=on:sos=all:ss=axioms:i=1198:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_afr=on:cs=on:e2e=on:hfsq=on:hfsqc=20:ntd=on:nwc=10.0:s2a=on:i=4753:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:fde=none:kws=inv_frequency:ntd=on:sos=on:i=4954:si=on:rtra=on_0");
    // Improves by expected 83.63371839116107 probs costing 239607 Mi
    // Sub-schedule for 480000Mi strat cap / 480000Mi overall limit
    quick.push("dis+10_4:1_avsq=on:e2e=on:fde=none:s2a=on:s2at=3.0:slsq=on:slsqc=1:i=19923:si=on:rtra=on_0");
    quick.push("dis+10_1:1_acc=on:fde=none:kws=inv_precedence:nwc=5.0:plsq=on:plsqc=1:plsqr=6,1:prag=on:s2a=on:i=13542:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_au=on:bsd=on:ins=3:plsq=on:plsqc=1:plsqr=1,1:s2a=on:s2at=3.0:sd=10:sp=weighted_frequency:ss=axioms:i=1655:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:av=off:fd=off:fde=unused:ntd=on:sos=on:sp=frequency:ss=axioms:i=2115:si=on:rtra=on_0");
    quick.push("lrs+10_1:128_cnfonf=off:e2e=on:fde=unused:hud=10:nm=16:pe=on:s2a=on:s2at=2.0:tgt=ground:i=2601:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_fe=off:hud=10:sos=on:ss=axioms:i=1016:si=on:rtra=on_0");
    quick.push("dis+10_1:3_au=on:cnfonf=lazy_pi_sigma_gen:i=1623:si=on:rtra=on_0");
    quick.push("ott+10_1:1_atotf=0.1:bd=off:cnfonf=off:cs=on:ins=2:nwc=3.0:sd=10:ss=axioms:i=3771:si=on:rtra=on_0");
    quick.push("lrs+1010_1:1_au=on:av=off:bsd=on:cnfonf=off:kws=arity_squared:sp=const_min:ss=axioms:i=925:si=on:rtra=on_0");
    quick.push("lrs+1010_1:1_c=on:cnfonf=lazy_gen:fe=off:ins=2:nwc=5.0:s2a=on:sp=occurrence:i=3973:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_aac=none:au=on:fde=unused:nm=2:sac=on:sos=all:i=14632:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_cnfonf=lazy_pi_sigma_gen:plsq=on:sos=on:i=9176:si=on:rtra=on_0");
    quick.push("ott+1010_16:1_au=on:cnfonf=off:e2e=on:i=12374:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_atotf=0.1:au=on:cnfonf=off:inj=on:piset=and:s2a=on:sos=on:i=1557:si=on:rtra=on_0");
    quick.push("dis-1010_1:1_au=on:avsq=on:e2e=on:nm=0:s2a=on:s2at=1.5:i=15824:si=on:rtra=on_0");
    quick.push("dis+1004_1:4_av=off:e2e=on:hud=3:prag=on:sos=on:ss=axioms:i=953:si=on:rtra=on_0");
    quick.push("lrs+1002_4:1_au=on:cnfonf=off:ins=1:nm=2:ntd=on:slsq=on:slsqc=4:sos=on:i=5996:si=on:rtra=on_0");
    quick.push("lrs+1002_2:3_avsq=on:fde=none:nwc=3.0:prag=on:sac=on:sd=2:sgt=32:sos=on:sp=unary_frequency:ss=axioms:i=14840:si=on:rtra=on_0");
    quick.push("ott+1010_1:64_au=on:cbe=off:cnfonf=off:nwc=10.0:s2a=on:ss=axioms:i=5101:si=on:rtra=on_0");
    quick.push("lrs+2_1:6_apa=on:cnfonf=off:e2e=on:fe=off:fsr=off:hud=1:prag=on:sos=on:sp=unary_frequency:i=9099:si=on:rtra=on_0");
    quick.push("dis+2_1:1_hflw=5:hfsq=on:hfsqc=8:hfsql=off:hfsqr=1,2:piset=pi_sigma:spb=goal:i=1042:si=on:rtra=on_0");
    quick.push("dis+1010_13:15_au=on:bd=off:bet=on:cnfonf=off:fe=axiom:hud=10:nm=0:ntd=on:nwc=5.0:sp=const_max:updr=off:i=1615:si=on:rtra=on_0");
    quick.push("ott+1010_1:1_au=on:bd=off:e2e=on:fde=none:ins=1:prag=on:sos=on:i=6247:si=on:rtra=on_0");
    quick.push("ott+1010_1:1_alpa=true:anc=none:atotf=0.1:au=on:cnfonf=off:ins=3:nm=64:sd=1:sp=occurrence:ss=axioms:st=5.0:i=6117:si=on:rtra=on_0");
    quick.push("lrs+1010_1:1_e2e=on:ntd=on:nwc=5.0:sac=on:sd=1:sgt=16:spb=units:ss=axioms:i=7827:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_au=on:e2e=on:hud=10:sd=4:sos=on:ss=axioms:st=2.0:i=3081:si=on:rtra=on_0");
    quick.push("lrs+10_5:1_au=on:av=off:bs=unit_only:bsr=unit_only:e2e=on:er=filter:fde=unused:lecc=1.3:nm=4:sp=frequency:i=11051:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:bd=off:e2e=on:ins=3:sos=on:ss=axioms:i=1761:si=on:rtra=on_0");
    quick.push("lrs+10_1:128_au=on:av=off:cnfonf=off:cond=fast:nm=6:sos=all:i=4759:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_au=on:kws=inv_precedence:nwc=5.0:sd=1:sgt=32:ss=axioms:i=1340:si=on:rtra=on_0");
    quick.push("lrs+1010_16:1_apa=on:au=on:bsr=on:cnfonf=off:fe=off:nm=32:prag=on:sac=on:sos=on:sp=unary_first:ss=axioms:i=1895:si=on:rtra=on_0");
    quick.push("lrs+21_16:1_au=on:bd=preordered:fde=none:ins=2:nwc=10.0:ss=axioms:st=2.0:i=12174:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_acc=on:au=on:bd=off:bsr=unit_only:cnfonf=off:fsr=off:nm=2:sos=all:i=4581:si=on:rtra=on_0");
    quick.push("lrs+1002_1:128_atotf=0.2:au=on:bd=off:cnfonf=off:plsq=on:plsqc=1:plsqr=1,2:prag=on:sd=1:ss=axioms:st=3.0:tgt=full:i=4854:si=on:rtra=on_0");
    quick.push("lrs+10_3:1_au=on:fsr=off:sd=1:sgt=100:ss=axioms:i=11200:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_e2e=on:nwc=5.0:sd=1:sgt=30:ss=axioms:i=870:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_bd=off:sd=2:sos=on:ss=axioms:i=1561:si=on:rtra=on_0");
    quick.push("lrs+1010_1:6_avsq=on:bd=off:cnfonf=off:ins=2:kws=precedence:ntd=on:sp=const_frequency:spb=units:tgt=full:i=4317:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_au=on:e2e=on:fd=off:sos=on:sp=unary_frequency:ss=axioms:i=4597:si=on:rtra=on_0");
    quick.push("dis+10_16:1_au=on:avsq=on:c=on:chr=on:nm=2:sac=on:sp=unary_first:ss=axioms:i=1781:si=on:rtra=on_0");
    quick.push("ott+1002_2:1_au=on:cnfonf=lazy_gen:fde=none:nm=32:s2a=on:sp=const_min:i=6520:si=on:rtra=on_0");
    quick.push("lrs+1010_8:1_au=on:cnfonf=lazy_pi_sigma_gen:fde=none:nwc=10.0:s2a=on:sac=on:i=1303:si=on:rtra=on_0");
    quick.push("dis+3_7:4_bsr=on:c=on:erd=off:fde=none:hud=10:lma=on:nwc=5.0:sac=on:sos=on:sp=frequency:i=8152:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_av=off:prag=on:sos=all:sp=frequency:i=7003:si=on:rtra=on_0");
    quick.push("lrs+1010_1:128_au=on:avsq=on:fsr=off:ins=3:kws=frequency:sos=all:i=1479:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_avsq=on:bsd=on:cnfonf=off:nm=10:piset=all_but_not_eq:s2a=on:s2at=6.0:sp=const_min:i=1368:si=on:rtra=on_0");
    quick.push("ott+1010_1:1_cnfonf=off:fd=off:rp=on:sac=on:sos=on:i=1264:si=on:rtra=on_0");
    quick.push("dis+10_1:1_acc=on:avsq=on:avsqr=1,16:kws=arity_squared:nm=20:sd=1:sp=const_frequency:ss=axioms:i=964:si=on:rtra=on_0");
    quick.push("dis+21_1:4_avsq=on:avsqr=924271,1048576:c=on:e2e=on:fs=off:fsr=off:piset=and:plsq=on:plsqr=32,1:sd=10:sos=on:sp=unary_first:ss=axioms:st=1.5:tnu=2:i=791:si=on:rtra=on_0");
    quick.push("dis+1002_1:2_au=on:bs=on:bsr=unit_only:c=on:fsr=off:hud=10:kws=inv_precedence:nm=6:ntd=on:nwc=10.0:sac=on:sos=on:i=1617:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_bs=on:cnfonf=lazy_not_be_gen:kws=inv_frequency:nwc=10.0:rawr=on:slsq=on:sp=weighted_frequency:uhcvi=on:i=2146:si=on:rtra=on_0");
    quick.push("dis+1002_16:1_au=on:ntd=on:sos=on:sp=frequency:uhcvi=on:i=8947:si=on:rtra=on_0");
    quick.push("lrs+21_7:1_bd=preordered:c=on:cnfonf=lazy_gen:fde=unused:fe=axiom:hud=10:piset=not:s2at=3.0:slsq=on:slsqr=9,7:ss=axioms:i=2167:si=on:rtra=on_0");
    quick.push("lrs+1666_1:1_bd=off:bet=on:bsd=on:bsr=unit_only:fde=none:nwc=10.0:sp=occurrence:i=2482:si=on:rtra=on_0");
    quick.push("lrs+1002_1:3_au=on:bs=unit_only:c=on:cnfonf=off:fde=none:kws=inv_arity_squared:nm=32:nwc=5.0:sos=on:i=12312:si=on:rtra=on_0");
    quick.push("dis+10_1:1_acc=on:avsq=on:e2e=on:ixr=off:s2a=on:sd=2:sp=occurrence:ss=axioms:i=724:si=on:rtra=on_0");
    quick.push("dis+1010_1:1_cnfonf=lazy_pi_sigma_gen:fe=off:piset=pi_sigma:plsq=on:plsqr=9,2:prag=on:sd=1:sgt=32:sp=occurrence:ss=axioms:uhcvi=on:i=3366:si=on:rtra=on_0");
    quick.push("dis+10_3:1_acc=on:avsq=on:bs=unit_only:cnfonf=off:fe=axiom:ins=3:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=1384:si=on:rtra=on_0");
    quick.push("ott+2_1:1_amm=off:atotf=0.4:cnfonf=off:fde=none:lma=on:nm=2:prag=on:sos=all:sp=const_max:tgt=ground:tnu=9:i=1540:si=on:rtra=on_0");
    quick.push("lrs+1010_16:1_acc=on:anc=all_dependent:avsq=on:fde=unused:hud=1:ins=2:piset=all_but_not_eq:prag=on:sac=on:i=61085:si=on:rtra=on_0");
    quick.push("lrs+10_5:1_cnfonf=lazy_not_gen_be_off:hud=5:sd=1:ss=axioms:i=1486:si=on:rtra=on_0");
    quick.push("dis+1004_1:5_avsq=on:cs=on:e2e=on:ins=2:sos=all:i=1188:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:bd=off:kws=precedence:sos=on:sp=frequency:ss=axioms:st=3.0:i=728:si=on:rtra=on_0");
    quick.push("dis+10_1:1_hud=5:nm=16:prag=on:sac=on:sos=on:ss=axioms:tnu=2:i=1141:si=on:rtra=on_0");
    quick.push("lrs+1002_4:1_au=on:cnfonf=off:er=filter:fde=none:ntd=on:nwc=10.0:i=20139:si=on:rtra=on_0");
    quick.push("dis+1010_73:128_bd=preordered:fsr=off:nwc=3.0:s2a=on:s2at=2.0:i=909:si=on:rtra=on_0");
    quick.push("dis+10_1:1_au=on:e2e=on:fde=unused:nwc=5.0:sac=on:sos=all:sp=const_frequency:i=30846:si=on:rtra=on_0");
    quick.push("lrs+1010_4:1_amm=off:awrs=decay:bsr=on:cbe=off:e2e=on:fde=none:fe=axiom:nwc=5.0:prag=on:sac=on:sd=1:spb=goal_then_units:ss=axioms:i=9747:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_sd=2:slsq=on:slsqc=1:ss=axioms:i=751:si=on:rtra=on_0");
    quick.push("lrs+10_97:429_c=on:cnfonf=lazy_gen:fe=axiom:ntd=on:s2a=on:sp=const_frequency:tgt=ground:i=1342:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_cbe=off:cnfonf=lazy_not_gen:nwc=13.0:prag=on:s2a=on:sp=weighted_frequency:i=1957:si=on:rtra=on_0");
    quick.push("lrs+21_1:128_acc=model:au=on:cbe=off:e2e=on:pe=on:piset=small_set:sos=on:sp=occurrence:ss=axioms:i=1179:si=on:rtra=on_0");
    quick.push("lrs+1002_1:16_abs=on:acc=model:au=on:bsr=unit_only:e2e=on:fde=none:sos=on:sp=const_frequency:i=5109:si=on:rtra=on_0");
    quick.push("ott+10_4:1_au=on:cnfonf=lazy_gen:fde=unused:kws=precedence:s2a=on:s2at=2.0:sd=1:ss=axioms:st=5.0:i=1125:si=on:rtra=on_0");
    quick.push("dis+10_1:128_atotf=0.1:fd=off:fsr=off:hflw=5:hfsq=on:hfsqc=5:hfsql=off:hfsqr=1,16:plsq=on:plsqr=9,8:tnu=1:i=1197:si=on:rtra=on_0");
    quick.push("ott+1666_4:1_au=on:bd=off:erd=off:ntd=on:sos=all:i=1038:si=on:rtra=on_0");
    quick.push("dis+21_1:1_au=on:e2e=on:hfsq=on:hfsql=off:lcm=reverse:nm=32:nwc=10.0:s2a=on:s2at=3.0:sd=1:ss=axioms:st=6.0:i=3014:si=on:rtra=on_0");
    quick.push("dis+1004_1:1_cnfonf=lazy_gen:fe=off:sd=1:sgt=30:slsq=on:ss=axioms:i=9638:si=on:rtra=on_0");
    quick.push("lrs+1010_3:1_bet=on:cnfonf=lazy_not_gen:fde=unused:nwc=10.0:sd=1:sp=unary_first:ss=axioms:i=6897:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_au=on:e2e=on:sos=all:ss=axioms:i=7846:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:fde=none:kws=inv_frequency:ntd=on:sos=on:i=12360:si=on:rtra=on_0");
    // Improves by expected 68.48008648144638 probs costing 479536 Mi
    // Sub-schedule for 960000Mi strat cap / 960000Mi overall limit
    quick.push("lrs+21_1:1_au=on:bsd=on:ins=3:plsq=on:plsqc=1:plsqr=1,1:s2a=on:s2at=3.0:sd=10:sp=weighted_frequency:ss=axioms:i=1655:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:av=off:fd=off:fde=unused:ntd=on:sos=on:sp=frequency:ss=axioms:i=1997:si=on:rtra=on_0");
    quick.push("ott+1010_3:1_bd=preordered:cbe=off:e2e=on:fe=axiom:hud=5:s2a=on:s2agt=60:slsq=on:ss=axioms:tnu=1:i=4783:si=on:rtra=on_0");
    quick.push("lrs+10_1:128_cnfonf=off:e2e=on:fde=unused:hud=10:nm=16:pe=on:s2a=on:s2at=2.0:tgt=ground:i=2601:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_fe=off:hud=10:sos=on:ss=axioms:i=1016:si=on:rtra=on_0");
    quick.push("ott+1010_1:1_au=on:av=off:cnfonf=lazy_not_gen_be_off:fe=axiom:kws=arity:nwc=5.0:ss=axioms:i=5570:si=on:rtra=on_0");
    quick.push("lrs+1010_1:1_au=on:av=off:bsd=on:cnfonf=off:kws=arity_squared:sp=const_min:ss=axioms:i=925:si=on:rtra=on_0");
    quick.push("lrs+1010_1:1_c=on:cnfonf=lazy_gen:fe=off:ins=2:nwc=5.0:s2a=on:sp=occurrence:i=3973:si=on:rtra=on_0");
    quick.push("dis+10_1:1_au=on:avsq=on:avsqr=16,1:fd=off:nm=2:sos=all:i=5800:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_aac=none:au=on:fde=unused:nm=2:sac=on:sos=all:i=68605:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_atotf=0.1:au=on:cnfonf=off:inj=on:piset=and:s2a=on:sos=on:i=1526:si=on:rtra=on_0");
    quick.push("dis+1010_1:1_fsd=on:hud=10:ntd=on:sp=reverse_arity:ss=axioms:i=13001:si=on:rtra=on_0");
    quick.push("lrs+1002_4:1_au=on:cnfonf=off:ins=1:nm=2:ntd=on:slsq=on:slsqc=4:sos=on:i=13141:si=on:rtra=on_0");
    quick.push("lrs+1010_1:64_acc=model:anc=all:bd=off:bsd=on:bsr=on:ins=3:ntd=on:prag=on:sos=all:i=40579:si=on:rtra=on_0");
    quick.push("lrs+1002_2:3_avsq=on:fde=none:nwc=3.0:prag=on:sac=on:sd=2:sgt=32:sos=on:sp=unary_frequency:ss=axioms:i=37097:si=on:rtra=on_0");
    quick.push("ott+1010_1:64_au=on:cbe=off:cnfonf=off:nwc=10.0:s2a=on:ss=axioms:i=5101:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_apa=on:au=on:cnfonf=off:e2e=on:hud=15:sos=on:i=1967:si=on:rtra=on_0");
    quick.push("ott+10_1:1_cbe=off:cnfonf=lazy_gen:ins=3:nwc=10.0:s2a=on:i=10040:si=on:rtra=on_0");
    quick.push("dis+2_1:1_hflw=5:hfsq=on:hfsqc=8:hfsql=off:hfsqr=1,2:piset=pi_sigma:spb=goal:i=1042:si=on:rtra=on_0");
    quick.push("dis+1002_2:3_aac=none:au=on:avsq=on:cbe=off:fde=none:lcm=predicate:nm=32:prag=on:sos=on:sp=unary_first:ss=axioms:st=2.0:i=22803:si=on:rtra=on_0");
    quick.push("dis+1010_13:15_au=on:bd=off:bet=on:cnfonf=off:fe=axiom:hud=10:nm=0:ntd=on:nwc=5.0:sp=const_max:updr=off:i=1615:si=on:rtra=on_0");
    quick.push("ott+1010_1:1_au=on:bd=off:e2e=on:fde=none:ins=1:prag=on:sos=on:i=4783:si=on:rtra=on_0");
    quick.push("ott+10_1:1_bd=preordered:bsr=on:cnfonf=lazy_gen:ntd=on:nwc=10.0:sims=off:sp=const_frequency:i=3527:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_au=on:avsq=on:hud=22:ins=3:ntd=on:nwc=3.0:s2a=on:sp=weighted_frequency:i=2579:si=on:rtra=on_0");
    quick.push("lrs+1010_1:1_e2e=on:ntd=on:nwc=5.0:sac=on:sd=1:sgt=16:spb=units:ss=axioms:i=65701:si=on:rtra=on_0");
    quick.push("lrs+1010_1:16_av=off:awrs=converge:cnfonf=off:nwc=4.0:plsq=on:plsqc=1:plsql=on:plsqr=3090729,1048576:ss=axioms:tgt=ground:i=69646:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_au=on:bd=off:cnfonf=off:fd=off:sos=all:i=9162:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_acc=on:au=on:bd=off:bsr=unit_only:cnfonf=off:fsr=off:nm=2:sos=all:i=40221:si=on:rtra=on_0");
    quick.push("lrs+1002_1:128_atotf=0.2:au=on:bd=off:cnfonf=off:plsq=on:plsqc=1:plsqr=1,2:prag=on:sd=1:ss=axioms:st=3.0:tgt=full:i=4186:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_e2e=on:fd=off:fe=off:prag=on:sos=on:i=3319:si=on:rtra=on_0");
    quick.push("dis+10_16:1_au=on:avsq=on:cnfonf=conj_eager:piset=equals:s2a=on:sp=occurrence:ss=axioms:i=3218:si=on:rtra=on_0");
    quick.push("lrs+1010_1:6_avsq=on:bd=off:cnfonf=off:ins=2:kws=precedence:ntd=on:sp=const_frequency:spb=units:tgt=full:i=4317:si=on:rtra=on_0");
    quick.push("ott+2_1:1_au=on:cnfonf=off:sos=all:ss=axioms:st=3.0:i=18139:si=on:rtra=on_0");
    quick.push("dis+10_3:2_cnfonf=lazy_pi_sigma_gen:fe=off:nwc=5.0:prag=on:s2a=on:s2at=3.0:sp=frequency:i=9898:si=on:rtra=on_0");
    quick.push("dis+21_8:1_au=on:cbe=off:cnfonf=off:hud=15:nwc=5.0:piset=not:sos=all:sp=unary_frequency:ss=axioms:i=6753:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_abs=on:au=on:cnfonf=off:fde=unused:inj=on:sos=on:i=3344:si=on:rtra=on_0");
    quick.push("ott+1010_8:1_au=on:bd=preordered:e2e=on:ins=3:kws=inv_frequency:nwc=10.0:sp=const_min:i=7911:si=on:rtra=on_0");
    quick.push("lrs+1010_8:1_au=on:cnfonf=lazy_pi_sigma_gen:fde=none:nwc=10.0:s2a=on:sac=on:i=4081:si=on:rtra=on_0");
    quick.push("dis+3_7:4_bsr=on:c=on:erd=off:fde=none:hud=10:lma=on:nwc=5.0:sac=on:sos=on:sp=frequency:i=1325:si=on:rtra=on_0");
    quick.push("lrs+10_5:1_avsq=on:avsqr=16,1:cnfonf=conj_eager:nwc=10.0:plsq=on:plsqc=1:plsqr=32,1:sd=2:spb=intro:ss=axioms:i=10373:si=on:rtra=on_0");
    quick.push("dis+10_4:1_atotf=0.3:bs=on:cnfonf=lazy_simp:fe=axiom:gs=on:nm=0:nwc=10.0:sp=const_frequency:i=23452:si=on:rtra=on_0");
    quick.push("lrs+32_1:2_au=on:cbe=off:lecc=0.75:s2a=on:s2at=6.0:tgt=ground:i=14769:si=on:rtra=on_0");
    quick.push("lrs+1010_1:128_au=on:avsq=on:fsr=off:ins=3:kws=frequency:sos=all:i=1479:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_c=on:cnfonf=lazy_not_gen:fe=off:hud=15:ins=2:nm=16:prag=on:uhcvi=on:i=17013:si=on:rtra=on_0");
    quick.push("lrs+21_8:1_cnfonf=lazy_not_gen:nm=2:nwc=10.0:plsq=on:plsqc=2:plsqr=6,1:prag=on:sgt=8:sp=unary_frequency:ss=axioms:i=9328:si=on:rtra=on_0");
    quick.push("ott+1002_14:1_c=on:cnfonf=lazy_gen:er=tagged:fe=axiom:s2a=on:ss=included:i=18879:si=on:rtra=on_0");
    quick.push("ott+1010_1:1_cnfonf=off:fd=off:rp=on:sac=on:sos=on:i=1264:si=on:rtra=on_0");
    quick.push("lrs+10_2:3_amm=off:au=on:bd=off:fde=unused:fe=off:fsr=off:nm=16:ntd=on:s2a=on:s2at=2.0:ss=axioms:st=3.0:i=9251:si=on:rtra=on_0");
    quick.push("ott+1002_2:1_au=on:ins=1:nm=2:sac=on:sos=all:i=2811:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_bs=on:cnfonf=lazy_not_be_gen:kws=inv_frequency:nwc=10.0:rawr=on:slsq=on:sp=weighted_frequency:uhcvi=on:i=2146:si=on:rtra=on_0");
    quick.push("ott+1002_23:4_fsd=on:ins=3:nwc=10.0:prag=on:i=1671:si=on:rtra=on_0");
    quick.push("dis+1002_16:1_au=on:ntd=on:sos=on:sp=frequency:uhcvi=on:i=2778:si=on:rtra=on_0");
    quick.push("lrs+21_7:1_bd=preordered:c=on:cnfonf=lazy_gen:fde=unused:fe=axiom:hud=10:piset=not:s2at=3.0:slsq=on:slsqr=9,7:ss=axioms:i=33343:si=on:rtra=on_0");
    quick.push("lrs+1666_1:1_bd=off:bet=on:bsd=on:bsr=unit_only:fde=none:nwc=10.0:sp=occurrence:i=2695:si=on:rtra=on_0");
    quick.push("dis+10_1:1_acc=on:avsq=on:e2e=on:ixr=off:s2a=on:sd=2:sp=occurrence:ss=axioms:i=13229:si=on:rtra=on_0");
    quick.push("dis+1010_1:1_cnfonf=lazy_pi_sigma_gen:fe=off:piset=pi_sigma:plsq=on:plsqr=9,2:prag=on:sd=1:sgt=32:sp=occurrence:ss=axioms:uhcvi=on:i=3366:si=on:rtra=on_0");
    quick.push("dis+10_3:1_acc=on:avsq=on:bs=unit_only:cnfonf=off:fe=axiom:ins=3:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=20702:si=on:rtra=on_0");
    quick.push("ott+2_1:1_amm=off:atotf=0.4:cnfonf=off:fde=none:lma=on:nm=2:prag=on:sos=all:sp=const_max:tgt=ground:tnu=9:i=1540:si=on:rtra=on_0");
    quick.push("dis+1004_1:5_avsq=on:cs=on:e2e=on:ins=2:sos=all:i=1188:si=on:rtra=on_0");
    quick.push("dis+1002_1:4_cnfonf=off:e2e=on:fde=unused:fsr=off:sac=on:sfv=off:tgt=full:i=15049:si=on:rtra=on_0");
    quick.push("ott+1010_44:25_afr=on:avsq=on:c=on:cnfonf=off:e2e=on:fd=preordered:hud=5:rawr=on:sp=frequency:spb=non_intro:tgt=full:tnu=1:i=7623:si=on:rtra=on_0");
    quick.push("dis+10_1:1_cnfonf=off:fe=off:nwc=10.0:s2a=on:s2agt=8:sd=1:ss=axioms:st=5.0:i=8973:si=on:rtra=on_0");
    quick.push("dis+1010_1:2_avsq=on:cnfonf=lazy_pi_sigma_gen:fe=axiom:hud=10:sd=2:ss=axioms:i=3633:si=on:rtra=on_0");
    quick.push("lrs+1010_16:1_au=on:cnfonf=lazy_gen:fsr=off:hfsq=on:hfsqr=1,32:sgt=16:ss=axioms:i=23300:si=on:rtra=on_0");
    quick.push("dis+1010_1:16_amm=sco:cnfonf=off:sd=1:ss=axioms:st=2.0:tgt=full:tnu=5:i=34824:si=on:rtra=on_0");
    quick.push("dis+2_1:1_bd=off:prag=on:sos=all:sp=frequency:ss=axioms:uhcvi=on:i=8613:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:bd=off:bet=on:fde=none:nm=20:sos=on:i=14011:si=on:rtra=on_0");
    quick.push("ott+2_4:1_au=on:cnfonf=lazy_pi_sigma_gen:hud=16:ins=3:nm=20:plsq=on:plsqc=1:plsqr=13,2:rawr=on:sp=reverse_arity:ss=axioms:st=3.0:i=24800:si=on:rtra=on_0");
    quick.push("lrs+10_16:1_au=on:bd=off:sac=on:sos=all:i=13248:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_av=off:c=on:cnfonf=off:kws=inv_precedence:piset=and:sd=1:ss=axioms:tgt=ground:tnu=2:i=20260:si=on:rtra=on_0");
    quick.push("dis+10_2:3_avsq=on:fd=off:fde=none:lcm=reverse:prag=on:sac=on:sos=on:i=4887:si=on:rtra=on_0");
    quick.push("ott+10_16:1_aac=none:au=on:cnfonf=off:nm=20:s2a=on:ss=axioms:i=24752:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_bd=off:bs=unit_only:bsd=on:cnfonf=off:fde=unused:fsr=off:hud=5:kws=inv_arity_squared:sp=const_min:i=2235:si=on:rtra=on_0");
    quick.push("dis+1002_8:1_acc=model:au=on:avsq=on:fd=off:hfsq=on:s2a=on:s2agt=16:sgt=10:sp=unary_frequency:ss=axioms:i=2286:si=on:rtra=on_0");
    quick.push("ott+10_4:1_au=on:cnfonf=lazy_gen:fde=unused:kws=precedence:s2a=on:s2at=2.0:sd=1:ss=axioms:st=5.0:i=1125:si=on:rtra=on_0");
    quick.push("lrs+1_1:1_acc=on:au=on:ccuc=first:erd=off:fde=none:fsr=off:nm=10:ntd=on:s2a=on:s2at=5.0:i=17270:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:sd=1:ss=axioms:i=2489:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_au=on:e2e=on:fde=none:plsq=on:plsqc=1:plsqr=32,1:sos=on:sp=const_frequency:ss=axioms:st=3.0:i=9026:si=on:rtra=on_0");
    quick.push("ott+1002_17:12_au=on:ins=3:sac=on:sd=3:sos=on:sp=occurrence:ss=axioms:i=2265:si=on:rtra=on_0");
    quick.push("dis+10_1:128_atotf=0.1:fd=off:fsr=off:hflw=5:hfsq=on:hfsqc=5:hfsql=off:hfsqr=1,16:plsq=on:plsqr=9,8:tnu=1:i=1197:si=on:rtra=on_0");
    quick.push("dis+10_1:3_au=on:av=off:cha=on:cnfonf=conj_eager:etr=on:fde=none:nwc=3.0:sp=weighted_frequency:i=12872:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:fde=none:kws=inv_frequency:ntd=on:sos=on:i=4954:si=on:rtra=on_0");
    // Improves by expected 49.127566684028515 probs costing 957834 Mi
    // Sub-schedule for 960000Mi strat cap / 960000Mi overall limit
    quick.push("dis+10_4:1_avsq=on:e2e=on:fde=none:s2a=on:s2at=3.0:slsq=on:slsqc=1:i=18622:si=on:rtra=on_0");
    quick.push("dis+1002_1:1_fe=off:hud=10:sos=on:ss=axioms:i=4533:si=on:rtra=on_0");
    quick.push("ott+1010_1:1_au=on:av=off:cnfonf=lazy_not_gen_be_off:fe=axiom:kws=arity:nwc=5.0:ss=axioms:i=5570:si=on:rtra=on_0");
    quick.push("lrs+1010_1:1_au=on:av=off:bsd=on:cnfonf=off:kws=arity_squared:sp=const_min:ss=axioms:i=44027:si=on:rtra=on_0");
    quick.push("dis+10_1:1_au=on:avsq=on:avsqr=16,1:fd=off:nm=2:sos=all:i=4753:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_aac=none:au=on:fde=unused:nm=2:sac=on:sos=all:i=6251:si=on:rtra=on_0");
    quick.push("dis-1010_1:1_au=on:avsq=on:e2e=on:nm=0:s2a=on:s2at=1.5:i=11778:si=on:rtra=on_0");
    quick.push("dis+1010_1:1_fsd=on:hud=10:ntd=on:sp=reverse_arity:ss=axioms:i=13001:si=on:rtra=on_0");
    quick.push("ott+10_15:2_au=on:avsq=on:cnfonf=lazy_pi_sigma_gen:cs=on:fde=none:ins=2:sp=unary_first:i=22053:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_au=on:cnfonf=off:e2e=on:piset=small_set:sac=on:sd=1:sos=all:ss=axioms:st=5.0:i=46089:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_bd=off:e2e=on:hud=15:s2a=on:sos=on:ss=axioms:tnu=1:i=5292:si=on:rtra=on_0");
    quick.push("dis+2_1:1_hflw=5:hfsq=on:hfsqc=8:hfsql=off:hfsqr=1,2:piset=pi_sigma:spb=goal:i=1805:si=on:rtra=on_0");
    quick.push("lrs+21_16:1_au=on:bd=preordered:fde=none:ins=2:nwc=10.0:ss=axioms:st=2.0:i=12174:si=on:rtra=on_0");
    quick.push("lrs+1010_8:1_acc=model:avsq=on:ccuc=small_ones:cnfonf=lazy_simp:nm=16:nwc=10.0:s2a=on:sac=on:sp=const_frequency:i=22253:si=on:rtra=on_0");
    quick.push("ott+10_1:1_afp=2000:avsq=on:bsr=unit_only:chr=on:ntd=on:piset=and:sos=on:sp=weighted_frequency:i=5377:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_atotf=0.0319537:au=on:sos=on:sp=unary_frequency:i=6236:si=on:rtra=on_0");
    quick.push("dis+10_3:2_cnfonf=lazy_pi_sigma_gen:fe=off:nwc=5.0:prag=on:s2a=on:s2at=3.0:sp=frequency:i=9898:si=on:rtra=on_0");
    quick.push("ott+10_4:1_e2e=on:fde=unused:nm=40:nwc=10.0:s2a=on:s2at=2.0:sp=unary_frequency:ss=axioms:i=28120:si=on:rtra=on_0");
    quick.push("lrs+10_2:1_fde=none:prag=on:sd=2:sgt=8:ss=axioms:tgt=ground:i=14683:si=on:rtra=on_0");
    quick.push("ott+1002_2:1_au=on:cnfonf=lazy_gen:fde=none:nm=32:s2a=on:sp=const_min:i=5696:si=on:rtra=on_0");
    quick.push("lrs+1010_8:1_au=on:cnfonf=lazy_pi_sigma_gen:fde=none:nwc=10.0:s2a=on:sac=on:i=85280:si=on:rtra=on_0");
    quick.push("dis+3_7:4_bsr=on:c=on:erd=off:fde=none:hud=10:lma=on:nwc=5.0:sac=on:sos=on:sp=frequency:i=5088:si=on:rtra=on_0");
    quick.push("lrs+10_5:1_avsq=on:avsqr=16,1:cnfonf=conj_eager:nwc=10.0:plsq=on:plsqc=1:plsqr=32,1:sd=2:spb=intro:ss=axioms:i=10373:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_c=on:cnfonf=lazy_not_gen:fe=off:hud=15:ins=2:nm=16:prag=on:uhcvi=on:i=17013:si=on:rtra=on_0");
    quick.push("ott+1002_14:1_c=on:cnfonf=lazy_gen:er=tagged:fe=axiom:s2a=on:ss=included:i=14123:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_bs=on:cnfonf=lazy_not_be_gen:kws=inv_frequency:nwc=10.0:rawr=on:slsq=on:sp=weighted_frequency:uhcvi=on:i=2146:si=on:rtra=on_0");
    quick.push("dis+1002_16:1_au=on:ntd=on:sos=on:sp=frequency:uhcvi=on:i=2778:si=on:rtra=on_0");
    quick.push("lrs+0_1:1_hfsq=on:hud=10:ins=2:prag=on:sac=on:sp=const_frequency:i=48810:si=on:rtra=on_0");
    quick.push("lrs+1666_1:1_bd=off:bet=on:bsd=on:bsr=unit_only:fde=none:nwc=10.0:sp=occurrence:i=2482:si=on:rtra=on_0");
    quick.push("lrs+1002_1:3_au=on:bs=unit_only:c=on:cnfonf=off:fde=none:kws=inv_arity_squared:nm=32:nwc=5.0:sos=on:i=12312:si=on:rtra=on_0");
    quick.push("dis+1010_1:1_cnfonf=lazy_pi_sigma_gen:fe=off:piset=pi_sigma:plsq=on:plsqr=9,2:prag=on:sd=1:sgt=32:sp=occurrence:ss=axioms:uhcvi=on:i=3366:si=on:rtra=on_0");
    quick.push("dis+10_3:1_acc=on:avsq=on:bs=unit_only:cnfonf=off:fe=axiom:ins=3:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=2946:si=on:rtra=on_0");
    quick.push("lrs+1010_16:1_acc=on:anc=all_dependent:avsq=on:fde=unused:hud=1:ins=2:piset=all_but_not_eq:prag=on:sac=on:i=90050:si=on:rtra=on_0");
    quick.push("ott+1010_44:25_afr=on:avsq=on:c=on:cnfonf=off:e2e=on:fd=preordered:hud=5:rawr=on:sp=frequency:spb=non_intro:tgt=full:tnu=1:i=7601:si=on:rtra=on_0");
    quick.push("dis+10_1:1_cnfonf=off:fe=off:nwc=10.0:s2a=on:s2agt=8:sd=1:ss=axioms:st=5.0:i=8973:si=on:rtra=on_0");
    quick.push("dis+1010_1:2_avsq=on:cnfonf=lazy_pi_sigma_gen:fe=axiom:hud=10:sd=2:ss=axioms:i=3633:si=on:rtra=on_0");
    quick.push("dis+21_1:1_au=on:c=on:cnfonf=off:e2e=on:ins=1:kws=precedence:ntd=on:sd=2:sos=on:ss=axioms:st=2.0:i=25272:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:bd=off:bet=on:fde=none:nm=20:sos=on:i=95997:si=on:rtra=on_0");
    quick.push("ott+2_1:1_abs=on:e2e=on:fsd=on:fsr=off:kws=inv_precedence:piset=not:prag=on:s2a=on:s2pl=no:sos=on:i=4759:si=on:rtra=on_0");
    quick.push("dis+10_1:1_au=on:e2e=on:fde=unused:nwc=5.0:sac=on:sos=all:sp=const_frequency:i=80153:si=on:rtra=on_0");
    quick.push("dis+10_2:3_avsq=on:fd=off:fde=none:lcm=reverse:prag=on:sac=on:sos=on:i=4887:si=on:rtra=on_0");
    quick.push("ott+10_16:1_aac=none:au=on:cnfonf=off:nm=20:s2a=on:ss=axioms:i=85427:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_e2e=on:prag=on:rawr=on:sos=on:sp=weighted_frequency:i=15115:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_au=on:fde=none:sos=all:i=11130:si=on:rtra=on_0");
    quick.push("ott+1002_17:12_au=on:ins=3:sac=on:sd=3:sos=on:sp=occurrence:ss=axioms:i=2265:si=on:rtra=on_0");
    quick.push("lrs+1010_3:1_bet=on:cnfonf=lazy_not_gen:fde=unused:nwc=10.0:sd=1:sp=unary_first:ss=axioms:i=6897:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_au=on:e2e=on:sos=all:ss=axioms:i=4492:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:fde=none:kws=inv_frequency:ntd=on:sos=on:i=11980:si=on:rtra=on_0");
    // Improves by expected 20.832310444427776 probs costing 953511 Mi
    // Sub-schedule for 960000Mi strat cap / 960000Mi overall limit
    quick.push("dis+1002_1:1_fe=off:hud=10:sos=on:ss=axioms:i=6230:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_au=on:bsd=on:c=on:fde=none:piset=equals:sac=on:sp=const_min:i=71177:si=on:rtra=on_0");
    quick.push("lrs+1010_1:1_c=on:cnfonf=lazy_gen:fe=off:ins=2:nwc=5.0:s2a=on:sp=occurrence:i=15983:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_aac=none:au=on:fde=unused:nm=2:sac=on:sos=all:i=26900:si=on:rtra=on_0");
    quick.push("lrs+1010_1:64_acc=model:anc=all:bd=off:bsd=on:bsr=on:ins=3:ntd=on:prag=on:sos=all:i=40579:si=on:rtra=on_0");
    quick.push("ott+10_15:2_au=on:avsq=on:cnfonf=lazy_pi_sigma_gen:cs=on:fde=none:ins=2:sp=unary_first:i=18776:si=on:rtra=on_0");
    quick.push("lrs+2_1:6_apa=on:cnfonf=off:e2e=on:fe=off:fsr=off:hud=1:prag=on:sos=on:sp=unary_frequency:i=9099:si=on:rtra=on_0");
    quick.push("lrs+21_1:1_bd=off:e2e=on:hud=15:s2a=on:sos=on:ss=axioms:tnu=1:i=5292:si=on:rtra=on_0");
    quick.push("dis+1002_2:3_aac=none:au=on:avsq=on:cbe=off:fde=none:lcm=predicate:nm=32:prag=on:sos=on:sp=unary_first:ss=axioms:st=2.0:i=22803:si=on:rtra=on_0");
    quick.push("lrs+1010_1:1_c=on:cnfonf=off:hud=15:rawr=on:sd=1:sos=all:ss=axioms:i=73159:si=on:rtra=on_0");
    quick.push("dis+1010_1:5_au=on:avsq=on:ins=3:nm=0:nwc=10.0:prag=on:sos=all:sp=const_frequency:i=11506:si=on:rtra=on_0");
    quick.push("lrs+10_5:1_au=on:av=off:bs=unit_only:bsr=unit_only:e2e=on:er=filter:fde=unused:lecc=1.3:nm=4:sp=frequency:i=18598:si=on:rtra=on_0");
    quick.push("lrs+21_16:1_au=on:bd=preordered:fde=none:ins=2:nwc=10.0:ss=axioms:st=2.0:i=12174:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_atotf=0.0319537:au=on:sos=on:sp=unary_frequency:i=6236:si=on:rtra=on_0");
    quick.push("ott+10_4:1_e2e=on:fde=unused:nm=40:nwc=10.0:s2a=on:s2at=2.0:sp=unary_frequency:ss=axioms:i=15576:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_c=on:cnfonf=off:hud=10:nm=10:ntd=on:s2a=on:sac=on:sgt=30:ss=included:i=41932:si=on:rtra=on_0");
    quick.push("lrs+10_1:1_bd=off:cnfonf=lazy_simp:fde=none:sp=occurrence:i=11232:si=on:rtra=on_0");
    quick.push("lrs+1010_8:1_au=on:cnfonf=lazy_pi_sigma_gen:fde=none:nwc=10.0:s2a=on:sac=on:i=188785:si=on:rtra=on_0");
    quick.push("dis+3_7:4_bsr=on:c=on:erd=off:fde=none:hud=10:lma=on:nwc=5.0:sac=on:sos=on:sp=frequency:i=9862:si=on:rtra=on_0");
    quick.push("lrs+21_8:1_cnfonf=lazy_not_gen:nm=2:nwc=10.0:plsq=on:plsqc=2:plsqr=6,1:prag=on:sgt=8:sp=unary_frequency:ss=axioms:i=9102:si=on:rtra=on_0");
    quick.push("ott+1002_14:1_c=on:cnfonf=lazy_gen:er=tagged:fe=axiom:s2a=on:ss=included:i=13047:si=on:rtra=on_0");
    quick.push("ott+1002_1:1_aac=none:au=on:bd=off:cnfonf=off:nm=0:s2at=3.0:s2pl=on:sac=on:sos=on:i=74823:si=on:rtra=on_0");
    quick.push("dis+10_3:1_acc=on:avsq=on:bs=unit_only:cnfonf=off:fe=axiom:ins=3:plsq=on:plsqc=1:plsqr=32,1:prag=on:i=20702:si=on:rtra=on_0");
    quick.push("lrs+20_1:1_au=on:bd=off:erd=off:fde=none:sos=on:i=111726:si=on:rtra=on_0");
    quick.push("dis+2_5:1_au=on:e2e=on:fsr=off:sos=on:sp=unary_first:ss=axioms:i=9441:si=on:rtra=on_0");
    quick.push("dis+10_1:1_cnfonf=off:fe=off:nwc=10.0:s2a=on:s2agt=8:sd=1:ss=axioms:st=5.0:i=8973:si=on:rtra=on_0");
    quick.push("dis+1010_1:2_avsq=on:cnfonf=lazy_pi_sigma_gen:fe=axiom:hud=10:sd=2:ss=axioms:i=3633:si=on:rtra=on_0");
    quick.push("dis+21_1:1_au=on:c=on:cnfonf=off:e2e=on:ins=1:kws=precedence:ntd=on:sd=2:sos=on:ss=axioms:st=2.0:i=25272:si=on:rtra=on_0");
    quick.push("dis+2_1:1_bd=off:prag=on:sos=all:sp=frequency:ss=axioms:uhcvi=on:i=8613:si=on:rtra=on_0");
    quick.push("lrs+10_16:1_au=on:bd=off:sac=on:sos=all:i=44526:si=on:rtra=on_0");
    quick.push("lrs+2_1:1_e2e=on:prag=on:rawr=on:sos=on:sp=weighted_frequency:i=15115:si=on:rtra=on_0");
    quick.push("lrs+1002_1:1_au=on:fde=none:kws=inv_frequency:ntd=on:sos=on:i=4811:si=on:rtra=on_0");
    // Improves by expected 11.519827354524478 probs costing 955651 Mi

    // Fri14 Overall score 3061.786675181413 probs on average / budget 3825887 Mi
    // Wed12 Overall score 3048.3069003468577 probs on average / budget 3833691 Mi
    // Tue11 Overall score 3039.0840598543527 probs on average / budget 3828761 Mi
    // Mon10b Overall score 3037.186917544398 probs on average / budget 3813568 Mi
    // Mon10a Overall score 3000.409829293265 probs on average / budget 3825232 Mi
    // Sun09 Overall score 2938.863699793977 probs on average / budget 1918256 Mi
    }
  } else { // if (property.higherOrder())
  // Sub-schedule for 10000Mi strat cap / 10000Mi overall limit
   quick.push("dis+1002_1:1_bd=off:fd=off:sos=on:i=601:si=on:rtra=on_0");
   quick.push("ott+1010_8:1_bsr=unit_only:drc=off:fsr=off:plsq=on:plsqc=1:plsqr=32,1:s2a=on:s2agt=32:urr=on:i=894:si=on:rtra=on_0");
   quick.push("dis+1011_4:1_av=off:nwc=10.0:sd=1:sgt=16:ss=axioms:i=563:si=on:rtra=on_0");
   quick.push("lrs+10_5:1_br=off:s2a=on:s2at=5.0:sd=2:ss=axioms:st=2.0:urr=on:i=596:si=on:rtra=on_0");
   quick.push("dis+21_2:3_drc=off:kws=precedence:s2a=on:s2agt=100:sgt=10:sp=unary_first:ss=axioms:i=628:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_fd=preordered:lecc=0.5:sos=on:sp=unary_frequency:to=lpo:urr=on:i=834:si=on:rtra=on_0");
   quick.push("dis-10_1:1_atotf=0.2:bd=off:drc=off:fd=preordered:fsr=off:nwc=3.0:sd=1:sp=const_frequency:spb=goal:ss=axioms:st=1.5:to=lpo:i=236:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_bd=off:drc=off:ins=3:nwc=10.0:s2a=on:ss=axioms:i=497:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_bd=preordered:fd=preordered:fsd=on:newcnf=on:plsq=on:plsql=on:slsq=on:sos=on:sp=weighted_frequency:spb=goal:to=lpo:i=362:si=on:rtra=on_0");
   quick.push("lrs+10_4:1_av=off:sd=2:sos=on:ss=axioms:urr=on:i=511:si=on:rtra=on_0");
   quick.push("dis+10_1:1_br=off:newcnf=on:nwc=10.0:s2a=on:ss=axioms:urr=on:i=246:si=on:rtra=on_0");
   quick.push("ott-2_2:3_av=off:drc=off:lcm=reverse:newcnf=on:nm=2:nwc=10.0:s2a=on:s2agt=10:to=lpo:urr=on:i=787:si=on:rtra=on_0");
   quick.push("lrs+1011_4:1_nwc=5.0:s2a=on:sp=const_min:ss=axioms:urr=on:i=647:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_ep=RS:fde=unused:slsq=on:slsqr=1,2:sp=occurrence:spb=goal:i=555:si=on:rtra=on_0");
   quick.push("dis-1011_1:3_fd=preordered:sd=1:sgt=100:ss=axioms:tgt=full:urr=ec_only:i=534:si=on:rtra=on_0");
   quick.push("ott+1011_8:1_br=off:drc=off:kws=precedence:nm=2:s2a=on:s2agt=16:sp=frequency:urr=on:i=1522:si=on:rtra=on_0");
   quick.push("dis+2_3:1_awrs=converge:awrsf=200:s2a=on:s2at=4.0:uhcvi=on:urr=on:i=2:si=on:rtra=on_0");
  // Improves by expected 5474.0882895272125 probs costing 9998 Mi
  // Sub-schedule for 20000Mi strat cap / 20000Mi overall limit
   quick.push("dis+2_1:1_nwc=10.0:sd=1:sgt=100:sp=frequency:ss=axioms:to=lpo:urr=on:i=731:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_ep=RS:erd=off:newcnf=on:sos=on:sp=weighted_frequency:i=301:si=on:rtra=on_0");
   quick.push("lrs+1011_8:1_cond=fast:drc=off:nwc=3.0:rawr=on:s2a=on:sac=on:slsq=on:slsqr=40,243:sp=const_frequency:to=lpo:uhcvi=on:i=1612:si=on:rtra=on_0");
   quick.push("dis+1011_1:2_anc=none:fd=preordered:kws=inv_arity_squared:nm=20:s2a=on:s2agt=100:s2pl=on:sd=2:slsq=on:slsqr=7,8:spb=intro:ss=axioms:st=5.0:i=2224:si=on:rtra=on_0");
   quick.push("ott+1010_1:1_amm=sco:ep=RST:sos=on:sp=reverse_arity:ss=axioms:st=1.5:urr=on:i=509:si=on:rtra=on_0");
   quick.push("dis+1011_1:3_av=off:bsd=on:kws=inv_arity_squared:plsq=on:plsqr=1,8:ss=axioms:tgt=full:i=2036:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_av=off:bd=off:sd=1:sos=all:ss=axioms:st=2.0:i=164:si=on:rtra=on_0");
   quick.push("lrs-1010_1:1_bd=off:sos=on:sp=weighted_frequency:to=lpo:i=373:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_avsq=on:bce=on:fde=unused:ins=2:kws=inv_frequency:sos=on:sp=reverse_arity:urr=on:i=232:si=on:rtra=on_0");
   quick.push("dis+10_1:2_newcnf=on:nm=2:sd=1:ss=axioms:i=162:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_nm=16:nwc=5.0:s2a=on:s2at=2.0:urr=on:i=780:si=on:rtra=on_0");
   quick.push("ott+10_1:1_av=off:erd=off:sos=on:ss=axioms:st=1.5:urr=on:i=197:si=on:rtra=on_0");
   quick.push("dis+1011_7:3_aac=none:bsr=unit_only:er=filter:kws=precedence:lma=on:nm=0:sd=2:sgt=16:sp=unary_first:ss=axioms:tgt=ground:i=425:si=on:rtra=on_0");
   quick.push("ott+1002_2:1_bd=off:kws=precedence:newcnf=on:rp=on:sos=on:sp=unary_first:ss=axioms:st=1.5:i=709:si=on:rtra=on_0");
   quick.push("dis+10_1:1_kws=inv_precedence:plsq=on:rawr=on:rp=on:slsq=on:sp=unary_first:i=46:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_acc=on:avsq=on:avsqc=2:s2a=on:s2at=1.5:ss=axioms:tgt=ground:i=291:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_av=off:kws=precedence:lcm=predicate:sos=on:sp=const_frequency:spb=goal:i=356:si=on:rtra=on_0");
   quick.push("ott+10_1:1_drc=off:s2a=on:sd=1:sp=weighted_frequency:ss=axioms:st=5.0:to=lpo:i=249:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_amm=off:sgt=8:sos=all:sp=unary_first:ss=axioms:to=lpo:i=234:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_nm=2:s2a=on:s2agt=100:sd=4:sgt=8:sos=all:ss=axioms:i=446:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_drc=off:nwc=10.0:s2a=on:s2at=3.0:sp=frequency:spb=non_intro:ss=axioms:to=lpo:i=244:si=on:rtra=on_0");
   quick.push("dis+10_1:1_avsq=on:s2a=on:s2agt=32:sac=on:i=428:si=on:rtra=on_0");
   quick.push("dis+10_3:1_av=off:nwc=5.0:s2a=on:s2agt=16:s2at=1.5:sd=1:sp=reverse_frequency:spb=goal:ss=axioms:st=5.0:i=368:si=on:rtra=on_0");
   quick.push("lrs-1010_1:1_ep=RSTC:sos=on:urr=ec_only:i=305:si=on:rtra=on_0");
   quick.push("lrs-32_1:1_fde=unused:kws=arity_squared:newcnf=on:nicw=on:nwc=5.0:rnwc=on:s2a=on:s2at=-1.0:urr=on:i=79:si=on:rtra=on_0");
   quick.push("lrs-1010_2:1_drc=off:kws=precedence:nwc=10.0:s2a=on:s2at=2.5:ss=axioms:st=3.0:i=452:si=on:rtra=on_0");
   quick.push("dis-1011_1:8_drc=off:fsr=off:lsd=10:nm=0:s2a=on:s2agt=16:sgt=10:spb=goal_then_units:ss=axioms:tgt=full:to=lpo:i=1411:si=on:rtra=on_0");
   quick.push("lrs-1002_1:1_bd=off:erd=off:sos=on:sp=unary_first:to=lpo:i=159:si=on:rtra=on_0");
   quick.push("lrs+1010_1:6_bd=off:flr=on:nm=2:s2a=on:sd=2:ss=axioms:i=344:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_avsq=on:drc=off:nwc=10.0:sp=frequency:to=lpo:i=332:si=on:rtra=on_0");
   quick.push("dis+21_1:1_ins=3:newcnf=on:sos=on:sp=weighted_frequency:to=lpo:i=250:si=on:rtra=on_0");
   quick.push("dis+10_1:4_av=off:fde=none:sos=on:sp=frequency:to=lpo:i=418:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_aac=none:bd=preordered:kws=precedence:nwc=10.0:sgt=16:sp=const_frequency:spb=goal_then_units:ss=axioms:i=728:si=on:rtra=on_0");
   quick.push("lrs-2_2:3_av=off:fsd=on:ins=1:lcm=predicate:nwc=8.0:s2a=on:s2at=5.0:slsq=on:slsqc=2:slsqr=2,1:sp=const_frequency:uhcvi=on:i=88:si=on:rtra=on_0");
   quick.push("ott+10_1:1_s2a=on:s2agt=16:sgt=10:slsq=on:slsqc=1:sp=const_min:spb=goal_then_units:ss=axioms:to=lpo:i=474:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_acc=on:avsq=on:avsqc=1:fsr=off:tgt=ground:i=204:si=on:rtra=on_0");
   quick.push("lrs-1011_1:20_sd=2:sgt=30:sp=frequency:spb=goal_then_units:ss=axioms:tgt=full:i=259:si=on:rtra=on_0");
   quick.push("ott+1666_5:1_aac=none:bs=unit_only:kws=inv_frequency:nwc=5.0:rawr=on:s2a=on:s2agt=64:sac=on:sp=occurrence:spb=goal:urr=on:i=1418:si=on:rtra=on_0");
  // Improves by expected 283.9457762984722 probs costing 20000 Mi
  // Sub-schedule for 30000Mi strat cap / 30000Mi overall limit
   quick.push("dis+1010_1:7_bd=off:kws=arity_squared:s2a=on:sp=const_frequency:tgt=ground:i=788:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_plsq=on:plsqr=32,1:rawr=on:sac=on:sos=all:sp=unary_frequency:to=lpo:i=201:si=on:rtra=on_0");
   quick.push("ott+1_8:1_add=large:nm=64:s2a=on:s2agt=5:s2at=3.0:tgt=full:uhcvi=on:urr=on:i=1258:si=on:rtra=on_0");
   quick.push("dis+10_3:1_drc=off:nwc=10.0:s2a=on:s2at=2.0:urr=on:i=2604:si=on:rtra=on_0");
   quick.push("ott+1002_5:1_drc=off:nwc=10.0:sp=const_min:spb=goal_then_units:to=lpo:urr=on:i=253:si=on:rtra=on_0");
   quick.push("dis+1011_4:1_anc=none:bd=off:fsr=off:lsd=10:s2at=4.0:sd=2:slsq=on:slsqc=1:sp=weighted_frequency:ss=axioms:st=5.0:i=302:si=on:rtra=on_0");
   quick.push("dis-1010_8:1_av=off:cond=fast:flr=on:kws=inv_frequency:nm=0:nwc=10.0:i=777:si=on:rtra=on_0");
   quick.push("lrs+10_3:1_bd=off:ins=3:nwc=3.0:sd=2:sgt=30:sp=frequency:ss=axioms:to=lpo:urr=on:i=1497:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_ep=RS:ss=axioms:i=822:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_alpa=false:bd=preordered:fde=none:newcnf=on:nm=64:s2at=5.0:slsq=on:slsqr=4,1:sos=on:sp=frequency:to=lpo:i=203:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_bd=off:drc=off:sos=on:urr=on:i=532:si=on:rtra=on_0");
   quick.push("lrs+2_3:1_bsr=unit_only:nwc=10.0:sos=all:sp=unary_frequency:ss=axioms:to=lpo:i=275:si=on:rtra=on_0");
   quick.push("dis+2_1:64_bd=off:fd=off:s2a=on:sac=on:sos=on:sp=const_frequency:i=208:si=on:rtra=on_0");
   quick.push("ott+2_4:1_br=off:bsd=on:drc=off:nm=2:sp=unary_first:urr=on:i=3039:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_fd=off:nm=2:sos=on:to=lpo:urr=on:i=416:si=on:rtra=on_0");
   quick.push("ott+10_1:128_s2a=on:sp=reverse_arity:spb=goal_then_units:to=lpo:i=65:si=on:rtra=on_0");
   quick.push("dis+1010_1:1024_bd=off:drc=off:newcnf=on:rawr=on:s2pl=on:sd=2:sgt=20:sp=const_frequency:spb=goal_then_units:ss=axioms:tgt=full:i=278:si=on:rtra=on_0");
   quick.push("dis+1002_5:1_add=large:amm=sco:gs=on:newcnf=on:s2a=on:s2agt=30:s2at=1.2:s2pl=no:slsq=on:slsqr=1,8:sp=reverse_arity:spb=intro:i=447:si=on:rtra=on_0");
   quick.push("dis+10_1:1_kws=inv_precedence:plsq=on:rawr=on:rp=on:slsq=on:sp=unary_first:i=59:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_ep=R:newcnf=on:sd=1:sos=on:ss=axioms:st=4.0:i=168:si=on:rtra=on_0");
   quick.push("dis+10_1:1_av=off:fd=off:plsq=on:plsqc=1:plsqr=32,1:s2a=on:s2at=5.0:s2pl=no:sd=1:sos=on:ss=axioms:i=222:si=on:rtra=on_0");
   quick.push("ott+10_1:1_drc=off:fd=preordered:s2a=on:s2at=2.0:sp=weighted_frequency:spb=goal:tgt=full:to=lpo:urr=on:i=471:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_bd=off:fsr=off:plsq=on:plsqr=32,1:sd=1:sos=on:ss=axioms:i=316:si=on:rtra=on_0");
   quick.push("dis+10_1:1_erd=off:sos=all:ss=axioms:i=247:si=on:rtra=on_0");
   quick.push("dis+1010_7:15_abs=on:anc=all:nm=0:sos=on:sp=weighted_frequency:ss=axioms:i=190:si=on:rtra=on_0");
   quick.push("lrs+2_1:3_atotf=0.1:bd=off:fd=off:sos=on:i=228:si=on:rtra=on_0");
   quick.push("lrs+1011_29:64_av=off:bs=unit_only:drc=off:kws=inv_frequency:lcm=reverse:sp=reverse_arity:tgt=full:i=780:si=on:rtra=on_0");
   quick.push("dis+2_1:7_av=off:fd=preordered:newcnf=on:nm=10:rp=on:sgt=16:sos=all:ss=axioms:i=612:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_av=off:bd=off:fsr=off:sos=on:ss=axioms:urr=on:i=1000:si=on:rtra=on_0");
   quick.push("dis-1011_1:1_av=off:fd=preordered:fsr=off:lcm=reverse:nm=2:nwc=10.0:s2a=on:s2agt=16:spb=goal:to=lpo:i=1217:si=on:rtra=on_0");
   quick.push("dis+11_1:1_atotf=0.1:nm=32:plsq=on:plsqc=1:plsql=on:plsqr=1,1:s2agt=64:slsq=on:slsqc=1:slsqr=2,1:sp=reverse_arity:spb=non_intro:ss=axioms:i=547:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_add=large:avsq=on:avsqr=21,4:bsr=unit_only:nm=16:nwc=6.0:plsq=on:plsqr=7452629,65536:rawr=on:s2a=on:slsq=on:slsqc=1:slsqr=1,4:sp=const_frequency:uhcvi=on:i=211:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_acc=on:drc=off:fd=preordered:s2a=on:sp=unary_first:to=lpo:i=333:si=on:rtra=on_0");
   quick.push("dis+1011_8:1_avsq=on:ep=RS:fsr=off:plsq=on:plsqr=32,1:ss=axioms:st=1.5:i=549:si=on:rtra=on_0");
   quick.push("dis+10_1:1_sd=1:sos=on:ss=axioms:st=2.0:i=218:si=on:rtra=on_0");
   quick.push("dis-1011_1:128_atotf=0.1:bd=off:fsr=off:s2a=on:slsq=on:slsqc=1:slsqr=1,2:sp=const_min:ss=axioms:st=5.0:tgt=full:to=lpo:i=314:si=on:rtra=on_0");
   quick.push("ott+1011_1:1_bd=off:flr=on:sos=on:i=317:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_ep=RS:fde=unused:slsq=on:slsqr=1,2:sp=occurrence:spb=goal:i=930:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_av=off:nwc=5.0:sd=1:sgt=8:ss=axioms:i=251:si=on:rtra=on_0");
   quick.push("dis+10_1:1_av=off:kws=precedence:lcm=reverse:sd=2:sgt=10:sp=const_max:ss=axioms:st=2.0:i=378:si=on:rtra=on_0");
   quick.push("dis+10_8:1_kws=precedence:newcnf=on:s2a=on:s2at=5.0:sd=2:slsq=on:slsqc=1:sp=unary_frequency:ss=axioms:st=3.0:urr=on:i=343:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_cond=fast:drc=off:erd=off:s2a=on:sac=on:slsq=on:slsql=off:ss=axioms:i=668:si=on:rtra=on_0");
   quick.push("dis-1011_1:3_fd=preordered:sd=1:sgt=100:ss=axioms:tgt=full:urr=ec_only:i=3535:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_acc=on:avsq=on:avsqc=5:avsqr=3,1:sd=1:sgt=10:spb=goal_then_units:ss=axioms:st=3.0:tgt=full:i=547:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_av=off:bd=off:lwlo=on:plsq=on:sos=all:sp=const_min:ss=axioms:st=5.0:to=lpo:i=179:si=on:rtra=on_0");
   quick.push("ott+2_1:64_aac=none:acc=model:awrs=decay:awrsf=5:br=off:rawr=on:sos=all:sp=weighted_frequency:tgt=ground:to=lpo:urr=ec_only:i=563:si=on:rtra=on_0");
   quick.push("dis+10_16:1_avsq=on:avsqr=1,16:fd=preordered:sgt=8:sos=all:ss=axioms:to=lpo:i=425:si=on:rtra=on_0");
   quick.push("lrs-10_1:1_av=off:bd=off:kws=precedence:sos=on:sp=unary_first:spb=goal:i=243:si=on:rtra=on_0");
  // Improves by expected 151.7500472259248 probs costing 29978 Mi
  // Sub-schedule for 60000Mi strat cap / 60000Mi overall limit
   quick.push("ott+1002_1:1_ep=RS:erd=off:newcnf=on:sos=on:sp=weighted_frequency:i=247:si=on:rtra=on_0");
   quick.push("dis+21_16:1_ep=RST:nm=3:slsq=on:ss=axioms:st=2.0:urr=on:i=704:si=on:rtra=on_0");
   quick.push("ott+1010_8:1_bsr=unit_only:drc=off:fsr=off:plsq=on:plsqc=1:plsqr=32,1:s2a=on:s2agt=32:urr=on:i=1694:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_av=off:rawr=on:s2a=on:slsq=on:slsqr=1,4:sp=unary_first:tgt=ground:i=1535:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_av=off:nm=32:plsq=on:sp=const_frequency:spb=goal:urr=on:i=497:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_bd=off:br=off:kws=arity_squared:newcnf=on:nm=40:nwc=10.0:sd=1:sp=unary_first:spb=goal_then_units:ss=axioms:urr=on:i=762:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_av=off:sos=on:sp=frequency:to=lpo:urr=on:i=423:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_flr=on:fsd=on:sd=2:ss=axioms:i=1254:si=on:rtra=on_0");
   quick.push("dis-11_1:1_avsq=on:avsqr=1,16:ep=R:gs=on:nm=32:plsq=on:plsqc=1:plsqr=19,1:sos=on:i=362:si=on:rtra=on_0");
   quick.push("dis+10_5:4_anc=none:bd=off:drc=off:fsr=off:ins=2:newcnf=on:sd=1:sgt=8:sp=unary_first:ss=axioms:tgt=full:i=1105:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_av=off:bd=off:bsr=unit_only:kws=frequency:lcm=reverse:nm=16:s2a=on:s2agt=8:sd=1:ss=axioms:st=3.0:urr=on:i=766:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_bd=off:kws=inv_frequency:lcm=reverse:nwc=10.0:plsq=on:plsql=on:plsqr=1,32:rawr=on:s2agt=16:s2at=3.0:sd=2:slsq=on:slsqc=2:sp=frequency:ss=axioms:st=5.0:i=312:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_bd=off:fd=off:nm=4:nwc=10.0:sd=1:ss=axioms:urr=on:i=355:si=on:rtra=on_0");
   quick.push("ott+1011_1:1_bd=off:drc=off:flr=on:kws=precedence:s2a=on:s2agt=32:sp=frequency:urr=on:i=608:si=on:rtra=on_0");
   quick.push("ott+10_1:1_av=off:erd=off:sos=on:ss=axioms:st=1.5:urr=on:i=197:si=on:rtra=on_0");
   quick.push("dis+2_4:1_acc=on:avsq=on:avsqc=1:avsqr=43,6:drc=off:fsr=off:kws=precedence:lcm=reverse:lma=on:newcnf=on:rawr=on:sac=on:sos=on:sp=weighted_frequency:i=865:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_nwc=10.0:sgt=8:ss=axioms:urr=on:i=819:si=on:rtra=on_0");
   quick.push("ott+10_1:128_s2a=on:sp=reverse_arity:spb=goal_then_units:to=lpo:i=159:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_anc=none:flr=on:kws=inv_arity:nm=0:nwc=5.0:sd=1:sgt=60:spb=units:ss=axioms:uhcvi=on:i=854:si=on:rtra=on_0");
   quick.push("ott+10_4:1_br=off:nwc=10.0:s2a=on:s2at=5.0:spb=goal:ss=axioms:st=2.0:tgt=full:to=lpo:urr=on:i=417:si=on:rtra=on_0");
   quick.push("ott+21_11537325:1048576_awrs=decay:awrsf=30:bd=off:nm=20:nwc=10.0:sd=10:sp=weighted_frequency:ss=axioms:st=2.0:urr=on:i=2221:si=on:rtra=on_0");
   quick.push("dis+21_1:1_anc=all:er=tagged:fsr=off:nm=16:s2agt=16:s2pl=on:sac=on:sos=on:sp=const_min:spb=goal_then_units:to=lpo:i=445:si=on:rtra=on_0");
   quick.push("dis+10_1:1_kws=inv_precedence:plsq=on:rawr=on:rp=on:slsq=on:sp=unary_first:i=59:si=on:rtra=on_0");
   quick.push("dis+1002_5:1_flr=on:plsq=on:s2a=on:s2agt=16:to=lpo:i=410:si=on:rtra=on_0");
   quick.push("dis+11_1:1_fsr=off:plsq=on:plsqr=3,1:s2a=on:s2agt=4:sac=on:sgt=8:ss=axioms:urr=on:i=1476:si=on:rtra=on_0");
   quick.push("lrs+10_5:1_avsq=on:avsqc=1:avsqr=1,16:lcm=reverse:s2a=on:s2agt=16:sp=frequency:urr=on:i=575:si=on:rtra=on_0");
   quick.push("dis+10_1:1_acc=on:br=off:s2a=on:s2agt=16:urr=on:i=1564:si=on:rtra=on_0");
   quick.push("lrs-1011_2:1_er=filter:flr=on:nwc=5.0:sac=on:sp=reverse_arity:to=lpo:i=482:si=on:rtra=on_0");
   quick.push("lrs+1002_1:2_ep=R:fsr=off:lwlo=on:s2a=on:sos=on:i=902:si=on:rtra=on_0");
   quick.push("ott+10_1:32_drc=off:kws=precedence:sd=1:spb=goal_then_units:ss=axioms:st=2.0:i=412:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_avsq=on:drc=off:ins=1:rawr=on:spb=non_intro:ss=axioms:st=2.0:tgt=ground:urr=on:i=563:si=on:rtra=on_0");
   quick.push("dis-1011_1:10_acc=on:drc=off:nm=2:s2a=on:s2at=3.0:sac=on:sd=2:sgt=10:ss=axioms:tgt=ground:i=2602:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_bd=off:kws=precedence:sd=1:slsq=on:sp=const_frequency:spb=intro:ss=axioms:tgt=full:i=462:si=on:rtra=on_0");
   quick.push("lrs+1010_1:3_newcnf=on:sp=unary_first:ss=axioms:st=3.0:urr=on:i=899:si=on:rtra=on_0");
   quick.push("lrs+10_1:40_av=off:bs=unit_only:rp=on:sd=1:ss=axioms:st=5.0:tgt=full:i=1668:si=on:rtra=on_0");
   quick.push("ott+10_8:1_acc=on:awrs=decay:awrsf=200:ccuc=first:drc=off:fde=none:newcnf=on:nm=10:nwc=6.0:sp=reverse_frequency:uhcvi=on:urr=on:i=788:si=on:rtra=on_0");
   quick.push("lrs+1002_1:2_av=off:sd=1:sos=all:ss=axioms:st=3.0:urr=ec_only:i=221:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_add=large:avsq=on:avsqr=21,4:bsr=unit_only:nm=16:nwc=6.0:plsq=on:plsqr=7452629,65536:rawr=on:s2a=on:slsq=on:slsqc=1:slsqr=1,4:sp=const_frequency:uhcvi=on:i=836:si=on:rtra=on_0");
   quick.push("ott+2_1:1_plsq=on:plsqr=32,1:rawr=on:sos=all:sp=weighted_frequency:spb=units:ss=axioms:to=lpo:i=616:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_av=off:ins=1:kws=inv_frequency:s2a=on:s2agt=8:sd=2:slsq=on:slsqc=1:slsqr=1,4:ss=axioms:st=5.0:tgt=ground:i=361:si=on:rtra=on_0");
   quick.push("lrs+2_1:67_av=off:fde=unused:kws=precedence:lcm=reverse:sos=on:i=208:si=on:rtra=on_0");
   quick.push("ott-2_2:3_av=off:drc=off:lcm=reverse:newcnf=on:nm=2:nwc=10.0:s2a=on:s2agt=10:to=lpo:urr=on:i=1514:si=on:rtra=on_0");
   quick.push("dis-1010_1:1_flr=on:kws=precedence:s2at=5.0:slsq=on:slsqc=1:sp=const_min:ss=axioms:st=2.0:tgt=ground:i=3668:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_drc=off:kws=precedence:s2a=on:urr=on:i=435:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_av=off:bd=off:erd=off:fsr=off:gs=on:sos=on:urr=on:i=625:si=on:rtra=on_0");
   quick.push("ott+21_35:3_drc=off:s2at=5.0:sac=on:slsq=on:slsqr=1,8:sp=reverse_frequency:ss=axioms:urr=on:i=7156:si=on:rtra=on_0");
   quick.push("dis+10_1:6_awrs=converge:drc=off:nm=4:s2a=on:sp=const_frequency:to=lpo:urr=on:i=459:si=on:rtra=on_0");
   quick.push("lrs+21_1:6_av=off:drc=off:fd=preordered:kws=frequency:nwc=5.0:sd=1:sgt=30:ss=axioms:st=3.0:tgt=ground:i=941:si=on:rtra=on_0");
   quick.push("lrs+2_1:4_er=filter:plsq=on:plsqc=1:plsqr=32,1:sp=frequency:spb=goal:ss=axioms:st=2.0:tgt=ground:urr=on:i=1189:si=on:rtra=on_0");
   quick.push("lrs+21_16:1_bd=off:cond=fast:kws=precedence:nm=2:s2a=on:sos=on:sp=unary_first:urr=ec_only:i=661:si=on:rtra=on_0");
   quick.push("dis+10_1:14_aac=none:fd=preordered:fsr=off:s2a=on:sac=on:sd=2:sgt=8:sp=weighted_frequency:ss=axioms:tgt=full:i=1613:si=on:rtra=on_0");
   quick.push("ott+10_1:1_s2a=on:s2agt=16:sgt=10:slsq=on:slsqc=1:sp=const_min:spb=goal_then_units:ss=axioms:to=lpo:i=1350:si=on:rtra=on_0");
   quick.push("lrs+3_1:6_anc=all:avsq=on:drc=off:nm=0:nwc=5.0:s2a=on:s2agt=8:spb=goal_then_units:to=lpo:urr=on:i=1116:si=on:rtra=on_0");
   quick.push("ott+1004_1:12_atotf=0.2:ins=1:sd=1:sgt=32:sp=frequency:ss=axioms:st=3.0:tgt=full:i=588:si=on:rtra=on_0");
   quick.push("ott+21_1:1_drc=off:s2a=on:s2agt=15:sp=reverse_arity:to=lpo:urr=on:i=671:si=on:rtra=on_0");
   quick.push("lrs+10_1:16_nwc=10.0:s2a=on:ss=axioms:st=2.0:urr=on:i=499:si=on:rtra=on_0");
   quick.push("lrs-1011_1:20_sd=2:sgt=30:sp=frequency:spb=goal_then_units:ss=axioms:tgt=full:i=1353:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_aac=none:fsr=off:sos=all:sp=const_frequency:ss=axioms:st=3.0:urr=on:i=1220:si=on:rtra=on_0");
   quick.push("dis+10_16:1_avsq=on:avsqr=1,16:fd=preordered:sgt=8:sos=all:ss=axioms:to=lpo:i=1207:si=on:rtra=on_0");
   quick.push("lrs+1002_3:1_plsq=on:plsqr=1,2:s2a=on:s2agt=8:sac=on:sgt=4:ss=axioms:i=683:si=on:rtra=on_0");
   quick.push("dis+1010_5568647:1048576_awrs=decay:awrsf=200:ins=3:kws=inv_arity:nwc=5.0:ss=axioms:i=450:si=on:rtra=on_0");
   quick.push("dis+1002_1:2_av=off:ep=RSTC:erd=off:kws=arity_squared:nwc=5.0:s2a=on:i=389:si=on:rtra=on_0");
   quick.push("lrs+1011_2:1_bd=off:br=off:s2a=on:s2agt=8:s2at=1.2:slsq=on:slsqc=1:slsqr=2,1:i=566:si=on:rtra=on_0");
  // Improves by expected 129.57230129213247 probs costing 59995 Mi
  // Sub-schedule for 120000Mi strat cap / 120000Mi overall limit
   quick.push("ott+11_1:1_av=off:bsr=unit_only:sos=all:i=2836:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_av=off:fd=off:nwc=5.0:sd=2:ss=axioms:st=3.0:to=lpo:i=2899:si=on:rtra=on_0");
   quick.push("dis+1002_2:1_anc=all_dependent:drc=off:newcnf=on:nm=32:s2a=on:s2agt=20:s2at=1.5:sp=reverse_arity:i=2258:si=on:rtra=on_0");
   quick.push("ott+1010_8:1_bsr=unit_only:drc=off:fsr=off:plsq=on:plsqc=1:plsqr=32,1:s2a=on:s2agt=32:urr=on:i=6540:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_fd=off:nwc=5.0:sos=on:spb=goal_then_units:to=lpo:i=343:si=on:rtra=on_0");
   quick.push("ott+1002_5:1_drc=off:nwc=10.0:sp=const_min:spb=goal_then_units:to=lpo:urr=on:i=2333:si=on:rtra=on_0");
   quick.push("ott+21_1:1_av=off:nwc=5.0:s2a=on:spb=intro:to=lpo:i=1038:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_fd=preordered:fde=unused:nm=10:s2at=5.0:slsq=on:slsqc=1:slsqr=4,1:spb=goal:ss=axioms:st=2.0:tgt=ground:to=lpo:i=433:si=on:rtra=on_0");
   quick.push("lrs+1011_3:2_lsd=30:nm=30:s2a=on:s2agt=15:slsq=on:spb=goal:to=lpo:i=1401:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_av=off:cond=fast:drc=off:kws=precedence:s2a=on:s2at=3.0:i=842:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_aac=none:avsq=on:avsqc=2:nm=40:sac=on:sos=all:urr=on:i=2039:si=on:rtra=on_0");
   quick.push("dis+10_1:8_av=off:fsd=on:fsr=off:s2a=on:sos=all:i=2503:si=on:rtra=on_0");
   quick.push("lrs+11_4:1_br=off:bs=on:drc=off:sp=const_frequency:spb=goal_then_units:ss=axioms:to=lpo:i=840:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_kws=arity_squared:nm=32:nwc=2.0:sac=on:i=687:si=on:rtra=on_0");
   quick.push("dis-11_1:1_avsq=on:avsqr=1,16:ep=R:gs=on:nm=32:plsq=on:plsqc=1:plsqr=19,1:sos=on:i=411:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_bd=off:kws=inv_frequency:lcm=reverse:nwc=10.0:plsq=on:plsql=on:plsqr=1,32:rawr=on:s2agt=16:s2at=3.0:sd=2:slsq=on:slsqc=2:sp=frequency:ss=axioms:st=5.0:i=312:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_ep=RS:ss=axioms:i=1165:si=on:rtra=on_0");
   quick.push("dis+10_1:1_kws=precedence:newcnf=on:nm=4:sos=on:sp=const_max:i=813:si=on:rtra=on_0");
   quick.push("lrs-1002_1:1_br=off:s2a=on:sp=unary_frequency:to=lpo:urr=on:i=1313:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_alpa=false:bd=preordered:fde=none:newcnf=on:nm=64:s2at=5.0:slsq=on:slsqr=4,1:sos=on:sp=frequency:to=lpo:i=203:si=on:rtra=on_0");
   quick.push("dis+1011_2:1_afr=on:fde=none:s2a=on:s2agt=20:i=2973:si=on:rtra=on_0");
   quick.push("ott+1011_1:1_bd=off:drc=off:flr=on:kws=precedence:s2a=on:s2agt=32:sp=frequency:urr=on:i=608:si=on:rtra=on_0");
   quick.push("lrs+10_16:1_abs=on:drc=off:nm=6:sac=on:sos=on:i=1041:si=on:rtra=on_0");
   quick.push("ott+10_1:1_av=off:erd=off:sos=on:ss=axioms:st=1.5:urr=on:i=1054:si=on:rtra=on_0");
   quick.push("dis+1011_5:1_gsp=on:ins=2:kws=inv_precedence:newcnf=on:sos=all:sp=const_max:spb=goal_then_units:i=697:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_fd=off:nm=2:sos=on:to=lpo:urr=on:i=1715:si=on:rtra=on_0");
   quick.push("dis+1010_5:1_av=off:kws=precedence:nm=64:plsq=on:s2a=on:s2at=2.0:sp=unary_frequency:ss=axioms:i=1866:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_erd=off:ins=1:kws=frequency:nm=40:sd=1:ss=axioms:st=5.0:tgt=ground:uhcvi=on:i=2009:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_anc=none:flr=on:kws=inv_arity:nm=0:nwc=5.0:sd=1:sgt=60:spb=units:ss=axioms:uhcvi=on:i=1951:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_acc=on:anc=none:bd=off:drc=off:erd=off:nwc=10.0:rnwc=on:s2a=on:s2at=2.0:urr=ec_only:i=691:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_nm=2:s2a=on:s2agt=16:sp=const_max:ss=axioms:st=2.0:urr=on:i=1009:si=on:rtra=on_0");
   quick.push("ott+2_8:1_abs=on:br=off:kws=frequency:nm=30:s2a=on:s2at=1.2:sp=frequency:tgt=full:urr=on:i=1046:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_av=off:ss=axioms:st=3.0:urr=on:i=1855:si=on:rtra=on_0");
   quick.push("lrs+1011_1:2_av=off:fsr=off:ins=1:lsd=10:nm=16:nwc=10.0:s2a=on:s2at=3.0:sp=unary_first:urr=on:i=519:si=on:rtra=on_0");
   quick.push("dis+1_1:1_atotf=0.18:fd=off:flr=on:newcnf=on:sos=on:i=355:si=on:rtra=on_0");
   quick.push("dis+1011_1:2_av=off:drc=off:flr=on:kws=precedence:sgt=8:ss=axioms:i=555:si=on:rtra=on_0");
   quick.push("dis+10_1:1_kws=inv_precedence:plsq=on:rawr=on:rp=on:slsq=on:sp=unary_first:i=932:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_cond=on:fd=preordered:flr=on:sos=on:sp=reverse_frequency:ss=axioms:i=338:si=on:rtra=on_0");
   quick.push("dis-1011_1:2_av=off:fde=unused:nwc=3.0:s2a=on:s2agt=100:tgt=full:i=1487:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_fd=preordered:lecc=0.5:sos=on:sp=unary_frequency:to=lpo:urr=on:i=1078:si=on:rtra=on_0");
   quick.push("dis+10_1:64_acc=on:bce=on:fde=none:nm=30:sd=3:sos=on:sp=frequency:ss=axioms:st=7.0:tgt=ground:to=lpo:i=905:si=on:rtra=on_0");
   quick.push("lrs-1011_1:32_av=off:bsd=on:drc=off:nm=10:sd=2:sgt=20:ss=axioms:st=1.5:tgt=ground:i=8118:si=on:rtra=on_0");
   quick.push("dis+10_4:1_cond=fast:fde=none:s2a=on:s2agt=32:s2at=1.2:i=1338:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_bd=preordered:fd=preordered:fsd=on:newcnf=on:plsq=on:plsql=on:slsq=on:sos=on:sp=weighted_frequency:spb=goal:to=lpo:i=695:si=on:rtra=on_0");
   quick.push("ott+21_1:1_drc=off:fde=unused:s2a=on:s2at=5.0:sp=const_min:urr=ec_only:i=664:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_afr=on:kws=precedence:nm=16:sp=weighted_frequency:spb=goal_then_units:ss=axioms:tgt=ground:i=3722:si=on:rtra=on_0");
   quick.push("dis+1011_1:5_av=off:bsr=unit_only:drc=off:sp=reverse_arity:tgt=full:i=4913:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_bd=off:nm=2:plsq=on:plsqc=2:sos=all:sp=const_frequency:i=397:si=on:rtra=on_0");
   quick.push("dis+21_5:1_drc=off:s2a=on:s2agt=16:s2at=5.0:tgt=full:uhcvi=on:urr=on:i=1397:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_acc=on:avsq=on:avsqc=5:drc=off:fde=none:kws=precedence:s2a=on:s2at=6.0:sp=frequency:spb=goal:tgt=ground:i=1081:si=on:rtra=on_0");
   quick.push("dis+10_1:1_s2agt=16:slsq=on:slsqc=1:sp=weighted_frequency:to=lpo:i=842:si=on:rtra=on_0");
   quick.push("lrs-1010_1:1_ep=RSTC:sos=on:urr=ec_only:i=849:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_bd=off:kws=precedence:sd=1:slsq=on:sp=const_frequency:spb=intro:ss=axioms:tgt=full:i=348:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_anc=none:ep=RS:nm=2:sd=10:sgt=10:sp=const_max:ss=axioms:i=1105:si=on:rtra=on_0");
   quick.push("lrs+1010_5:1_fde=unused:ins=3:newcnf=on:nwc=6.0:s2a=on:s2at=3.0:spb=intro:i=2557:si=on:rtra=on_0");
   quick.push("dis+11_1:3_avsq=on:avsql=on:bd=off:drc=off:fd=preordered:kws=inv_frequency:lma=on:newcnf=on:sp=reverse_frequency:tgt=ground:uhcvi=on:i=4384:si=on:rtra=on_0");
   quick.push("dis+1011_1:4_avsq=on:bd=off:kws=inv_frequency:nwc=5.0:s2a=on:sac=on:sp=const_frequency:i=1788:si=on:rtra=on_0");
   quick.push("ott+2_2:1_br=off:drc=off:ins=3:newcnf=on:nm=0:sp=const_frequency:ss=axioms:st=3.0:tgt=full:urr=on:i=5487:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_cond=fast:nm=10:sd=2:spb=intro:ss=axioms:i=1162:si=on:rtra=on_0");
   quick.push("lrs+10_4:1_bd=preordered:nwc=5.0:sd=1:ss=axioms:urr=on:i=2880:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_acc=on:avsq=on:avsqc=1:fsr=off:tgt=ground:i=182:si=on:rtra=on_0");
   quick.push("dis-1_1:1_abs=on:bd=off:sos=on:sp=frequency:to=lpo:i=481:si=on:rtra=on_0");
   quick.push("dis+1011_3:1_av=off:fsr=off:nwc=10.0:sgt=16:sp=unary_first:ss=axioms:st=2.0:i=1980:si=on:rtra=on_0");
   quick.push("ott+21_1:1_drc=off:s2a=on:s2agt=15:sp=reverse_arity:to=lpo:urr=on:i=1077:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_bd=off:nm=16:s2a=on:s2agt=16:sp=frequency:to=lpo:i=732:si=on:rtra=on_0");
   quick.push("lrs-1011_1:20_sd=2:sgt=30:sp=frequency:spb=goal_then_units:ss=axioms:tgt=full:i=237:si=on:rtra=on_0");
   quick.push("ott+1011_8:1_br=off:drc=off:kws=precedence:nm=2:s2a=on:s2agt=16:sp=frequency:urr=on:i=7121:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_av=off:cond=fast:gs=on:ins=3:sos=all:sp=frequency:to=lpo:i=1438:si=on:rtra=on_0");
   quick.push("lrs+1011_2:13_av=off:awrs=decay:awrsf=300:bd=off:fd=off:fsr=off:kws=inv_precedence:s2a=on:s2at=1.5:slsq=on:spb=goal:i=1103:si=on:rtra=on_0");
   quick.push("ott+21_29:3_erd=off:s2a=on:s2at=1.5:sac=on:sd=1:ss=axioms:st=6.0:to=lpo:urr=on:i=770:si=on:rtra=on_0");
   quick.push("lrs-11_1:1_br=off:drc=off:kws=precedence:lsd=50:slsq=on:slsql=off:slsqr=1,2:spb=intro:ss=axioms:i=492:si=on:rtra=on_0");
   quick.push("dis-1010_1:6_fde=unused:ins=2:rawr=on:slsq=on:slsqc=1:slsqr=11,4:sp=reverse_arity:spb=non_intro:tgt=ground:i=760:si=on:rtra=on_0");
   quick.push("dis+10_1:1_s2a=on:sp=occurrence:to=lpo:i=293:si=on:rtra=on_0");
   quick.push("lrs+1010_1:6_anc=all:awrs=decay:bs=on:erd=off:ins=1:sd=1:sgt=16:sos=all:spb=goal:ss=axioms:st=1.5:to=lpo:i=1323:si=on:rtra=on_0");
   quick.push("dis+21_1:8_bs=unit_only:fsr=off:kws=inv_arity_squared:sos=on:sp=unary_frequency:i=1386:si=on:rtra=on_0");
   quick.push("dis+2_8:1_aac=none:abs=on:bd=off:er=tagged:fde=none:fs=off:fsr=off:sfv=off:sos=all:to=lpo:i=566:si=on:rtra=on_0");
   quick.push("dis+1002_1:2_av=off:ep=RSTC:erd=off:kws=arity_squared:nwc=5.0:s2a=on:i=389:si=on:rtra=on_0");
  // Improves by expected 107.39643521475446 probs costing 119873 Mi
  // Sub-schedule for 240000Mi strat cap / 240000Mi overall limit
   quick.push("dis+1010_1:7_bd=off:kws=arity_squared:s2a=on:sp=const_frequency:tgt=ground:i=537:si=on:rtra=on_0");
   quick.push("dis+10_1:1_fd=off:ins=2:lma=on:sos=all:spb=goal_then_units:i=369:si=on:rtra=on_0");
   quick.push("ott+1_8:1_add=large:nm=64:s2a=on:s2agt=5:s2at=3.0:tgt=full:uhcvi=on:urr=on:i=1447:si=on:rtra=on_0");
   quick.push("dis-10_1:3_acc=model:awrs=decay:br=off:bsd=on:fd=preordered:nm=2:s2a=on:s2at=3.0:tgt=full:to=lpo:i=3738:si=on:rtra=on_0");
   quick.push("dis+1011_1:3_av=off:bsd=on:kws=inv_arity_squared:plsq=on:plsqr=1,8:ss=axioms:tgt=full:i=10094:si=on:rtra=on_0");
   quick.push("dis+11_1:7_sac=on:sd=2:ss=axioms:st=4.0:i=1715:si=on:rtra=on_0");
   quick.push("ott+4_1:1024_bd=off:plsq=on:plsqc=1:plsqr=7,1:sd=2:ss=axioms:i=383:si=on:rtra=on_0");
   quick.push("lrs+1011_1:24_atotf=0.2:bd=off:s2a=on:s2agt=60:sgt=20:ss=axioms:tgt=ground:i=8128:si=on:rtra=on_0");
   quick.push("lrs+10_7:4_acc=on:drc=off:kws=inv_frequency:nm=16:sp=weighted_frequency:spb=intro:ss=axioms:tgt=full:i=476:si=on:rtra=on_0");
   quick.push("ott+1010_8:1_bsr=unit_only:drc=off:fsr=off:plsq=on:plsqc=1:plsqr=32,1:s2a=on:s2agt=32:urr=on:i=893:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_fd=off:nwc=5.0:sos=on:spb=goal_then_units:to=lpo:i=343:si=on:rtra=on_0");
   quick.push("ott+1002_5:1_drc=off:nwc=10.0:sp=const_min:spb=goal_then_units:to=lpo:urr=on:i=1356:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_ep=RS:sos=on:ss=axioms:st=1.5:urr=on:i=3901:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_bd=off:br=off:kws=arity_squared:newcnf=on:nm=40:nwc=10.0:sd=1:sp=unary_first:spb=goal_then_units:ss=axioms:urr=on:i=1084:si=on:rtra=on_0");
   quick.push("lrs+11_2:1_av=off:drc=off:lsd=50:nm=2:nwc=5.0:s2a=on:s2agt=20:i=4880:si=on:rtra=on_0");
   quick.push("lrs+1011_5:1_av=off:lwlo=on:nwc=3.0:tgt=ground:i=10632:si=on:rtra=on_0");
   quick.push("lrs+11_4:1_br=off:bs=on:drc=off:sp=const_frequency:spb=goal_then_units:ss=axioms:to=lpo:i=840:si=on:rtra=on_0");
   quick.push("dis+1004_1:1_av=off:drc=off:fd=preordered:flr=on:s2a=on:s2agt=16:sp=const_frequency:urr=ec_only:i=2191:si=on:rtra=on_0");
   quick.push("dis-1010_8:1_av=off:cond=fast:flr=on:kws=inv_frequency:nm=0:nwc=10.0:i=546:si=on:rtra=on_0");
   quick.push("ott+2_1:1_lcm=predicate:s2a=on:s2agt=4:s2at=2.0:urr=on:i=6322:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_bs=on:fde=unused:flr=on:s2a=on:s2at=2.0:i=1860:si=on:rtra=on_0");
   quick.push("dis+10_5:4_anc=none:bd=off:drc=off:fsr=off:ins=2:newcnf=on:sd=1:sgt=8:sp=unary_first:ss=axioms:tgt=full:i=1834:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_av=off:bd=off:bsr=unit_only:kws=frequency:lcm=reverse:nm=16:s2a=on:s2agt=8:sd=1:ss=axioms:st=3.0:urr=on:i=713:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_bd=off:kws=inv_frequency:lcm=reverse:nwc=10.0:plsq=on:plsql=on:plsqr=1,32:rawr=on:s2agt=16:s2at=3.0:sd=2:slsq=on:slsqc=2:sp=frequency:ss=axioms:st=5.0:i=312:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_ep=RS:ss=axioms:i=1165:si=on:rtra=on_0");
   quick.push("dis+1010_1:24_kws=arity_squared:sac=on:sgt=20:sp=unary_frequency:ss=axioms:tgt=full:i=11705:si=on:rtra=on_0");
   quick.push("lrs+10_8:1_drc=off:ins=1:plsq=on:plsqc=1:plsqr=32,1:urr=on:i=3162:si=on:rtra=on_0");
   quick.push("ott+1011_1:1_bd=off:drc=off:flr=on:kws=precedence:s2a=on:s2agt=32:sp=frequency:urr=on:i=2837:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_amm=off:bs=unit_only:fd=preordered:kws=inv_frequency:lcm=predicate:newcnf=on:spb=goal:tgt=ground:i=10191:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_av=off:ins=1:newcnf=on:nwc=10.0:s2a=on:s2at=2.0:ss=axioms:i=4466:si=on:rtra=on_0");
   quick.push("lrs-3_3:1_slsq=on:sp=frequency:to=lpo:urr=on:i=1192:si=on:rtra=on_0");
   quick.push("ott+1011_5:1_atotf=0.2:nm=0:sgt=10:ss=axioms:tgt=ground:i=2284:si=on:rtra=on_0");
   quick.push("dis-1011_1:1_av=off:fd=off:nm=2:slsq=on:slsql=off:spb=goal_then_units:ss=axioms:st=5.0:uhcvi=on:i=5106:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_fde=unused:flr=on:gsp=on:lwlo=on:nwc=10.0:sd=2:spb=units:ss=axioms:st=2.0:urr=on:i=2348:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_anc=none:flr=on:kws=inv_arity:nm=0:nwc=5.0:sd=1:sgt=60:spb=units:ss=axioms:uhcvi=on:i=1715:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_acc=on:anc=none:bd=off:drc=off:erd=off:nwc=10.0:rnwc=on:s2a=on:s2at=2.0:urr=ec_only:i=691:si=on:rtra=on_0");
   quick.push("dis+1011_1:14_ep=R:fsr=off:kws=inv_arity:lsd=50:nwc=5.0:s2a=on:s2agt=60:sp=weighted_frequency:i=1769:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_ep=R:nm=0:slsq=on:slsqr=1,16:i=8263:si=on:rtra=on_0");
   quick.push("dis+10_16:1_drc=off:sd=2:sos=on:sp=const_min:ss=axioms:to=lpo:i=2535:si=on:rtra=on_0");
   quick.push("dis+1010_16:1_sos=on:sp=const_frequency:to=lpo:i=6745:si=on:rtra=on_0");
   quick.push("dis+1010_1:24_amm=sco:nm=0:s2a=on:s2at=2.0:sp=unary_first:tgt=ground:i=2461:si=on:rtra=on_0");
   quick.push("ott+2_8:1_abs=on:br=off:kws=frequency:nm=30:s2a=on:s2at=1.2:sp=frequency:tgt=full:urr=on:i=1046:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_br=off:plsq=on:plsqr=4779363,1048576:sd=2:sos=all:ss=axioms:urr=on:i=3830:si=on:rtra=on_0");
   quick.push("dis+1002_5:1_add=large:amm=sco:gs=on:newcnf=on:s2a=on:s2agt=30:s2at=1.2:s2pl=no:slsq=on:slsqr=1,8:sp=reverse_arity:spb=intro:i=375:si=on:rtra=on_0");
   quick.push("lrs+1011_1:2_av=off:fsr=off:ins=1:lsd=10:nm=16:nwc=10.0:s2a=on:s2at=3.0:sp=unary_first:urr=on:i=2292:si=on:rtra=on_0");
   quick.push("lrs+10_5:1_br=off:s2a=on:s2at=5.0:sd=2:ss=axioms:st=2.0:urr=on:i=2461:si=on:rtra=on_0");
   quick.push("dis+1011_1:2_av=off:drc=off:flr=on:kws=precedence:sgt=8:ss=axioms:i=555:si=on:rtra=on_0");
   quick.push("dis+10_1:1_kws=inv_precedence:plsq=on:rawr=on:rp=on:slsq=on:sp=unary_first:i=932:si=on:rtra=on_0");
   quick.push("dis+21_141:35_awrs=decay:awrsf=110:kws=precedence:lcm=reverse:lma=on:nwc=10.0:s2a=on:s2at=3.0:sp=reverse_arity:i=2411:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_av=off:bd=off:br=off:cond=fast:nwc=3.0:s2a=on:s2at=3.0:i=3870:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_atotf=0.00189482:drc=off:fsr=off:s2a=on:sd=1:ss=axioms:st=2.0:i=2594:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_bd=preordered:fd=preordered:fsd=on:newcnf=on:plsq=on:plsql=on:slsq=on:sos=on:sp=weighted_frequency:spb=goal:to=lpo:i=4502:si=on:rtra=on_0");
   quick.push("ott+21_1:1_drc=off:fde=unused:s2a=on:s2at=5.0:sp=const_min:urr=ec_only:i=664:si=on:rtra=on_0");
   quick.push("ott+10_1:1_bd=off:nm=30:slsq=on:slsqr=1,2:sp=unary_first:ss=axioms:st=2.0:uhcvi=on:urr=on:i=5300:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_amm=off:sgt=8:sos=all:sp=unary_first:ss=axioms:to=lpo:i=1515:si=on:rtra=on_0");
   quick.push("lrs-1011_8:1_amm=off:avsq=on:avsqr=1,16:bd=off:sos=on:sp=const_frequency:spb=non_intro:to=lpo:uhcvi=on:i=551:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_nm=2:s2a=on:s2agt=100:sd=4:sgt=8:sos=all:ss=axioms:i=481:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_anc=none:ep=RS:kws=frequency:lcm=reverse:rp=on:s2a=on:sos=on:sp=occurrence:spb=goal:tgt=ground:updr=off:i=481:si=on:rtra=on_0");
   quick.push("dis+21_5:1_acc=on:br=off:lcm=predicate:newcnf=on:nicw=on:nm=2:sp=unary_first:ss=axioms:st=1.5:urr=on:i=3391:si=on:rtra=on_0");
   quick.push("dis-1011_1:28_av=off:drc=off:fde=unused:s2a=on:tgt=full:i=3375:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_avsq=on:drc=off:ins=1:rawr=on:spb=non_intro:ss=axioms:st=2.0:tgt=ground:urr=on:i=1807:si=on:rtra=on_0");
   quick.push("dis+1002_8:1_s2a=on:s2agt=10:i=1986:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_acc=on:avsq=on:avsqc=5:drc=off:fde=none:kws=precedence:s2a=on:s2at=6.0:sp=frequency:spb=goal:tgt=ground:i=4248:si=on:rtra=on_0");
   quick.push("dis+10_1:1_s2agt=16:slsq=on:slsqc=1:sp=weighted_frequency:to=lpo:i=410:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_bd=off:kws=precedence:sd=1:slsq=on:sp=const_frequency:spb=intro:ss=axioms:tgt=full:i=1780:si=on:rtra=on_0");
   quick.push("dis-1011_1:1_av=off:fd=preordered:fsr=off:lcm=reverse:nm=2:nwc=10.0:s2a=on:s2agt=16:spb=goal:to=lpo:i=1903:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_anc=none:ep=RS:nm=2:sd=10:sgt=10:sp=const_max:ss=axioms:i=971:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_add=large:avsq=on:avsqr=21,4:bsr=unit_only:nm=16:nwc=6.0:plsq=on:plsqr=7452629,65536:rawr=on:s2a=on:slsq=on:slsqc=1:slsqr=1,4:sp=const_frequency:uhcvi=on:i=836:si=on:rtra=on_0");
   quick.push("lrs+1011_4:1_nwc=5.0:s2a=on:sp=const_min:ss=axioms:urr=on:i=1660:si=on:rtra=on_0");
   quick.push("lrs+10_4:1_acc=model:anc=all:bd=off:flr=on:kws=inv_frequency:nm=16:sac=on:sos=all:i=3697:si=on:rtra=on_0");
   quick.push("lrs+1010_1:3_newcnf=on:spb=non_intro:ss=axioms:st=2.0:urr=on:i=1140:si=on:rtra=on_0");
   quick.push("ott+21_1:1_bsr=unit_only:fsr=off:kws=inv_arity:nwc=10.0:rawr=on:sos=all:sp=frequency:i=1566:si=on:rtra=on_0");
   quick.push("lrs+21_1:7_drc=off:gsp=on:sd=1:sgt=64:ss=axioms:urr=on:i=4815:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_atotf=0.4:fde=unused:nm=2:sos=all:to=lpo:uhcvi=on:i=4977:si=on:rtra=on_0");
   quick.push("lrs+21_1:6_av=off:drc=off:fd=preordered:kws=frequency:nwc=5.0:sd=1:sgt=30:ss=axioms:st=3.0:tgt=ground:i=941:si=on:rtra=on_0");
   quick.push("ott+1004_8:1_fd=preordered:sac=on:ss=axioms:st=3.0:to=lpo:i=3117:si=on:rtra=on_0");
   quick.push("lrs+3_1:6_anc=all:avsq=on:drc=off:nm=0:nwc=5.0:s2a=on:s2agt=8:spb=goal_then_units:to=lpo:urr=on:i=2430:si=on:rtra=on_0");
   quick.push("lrs+10_1:8_drc=off:slsq=on:slsqc=1:sp=const_min:ss=axioms:to=lpo:i=493:si=on:rtra=on_0");
   quick.push("lrs+2_1:1_bd=off:fd=off:sfv=off:sos=all:to=lpo:i=3997:si=on:rtra=on_0");
   quick.push("dis+1011_3:1_av=off:fsr=off:nwc=10.0:sgt=16:sp=unary_first:ss=axioms:st=2.0:i=1197:si=on:rtra=on_0");
   quick.push("lrs+1002_16:1_flr=on:nwc=3.0:s2a=on:s2agt=16:sp=const_min:spb=goal:to=lpo:urr=on:i=1399:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_aac=none:fsr=off:sos=all:sp=const_frequency:ss=axioms:st=3.0:urr=on:i=1072:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_bd=off:ins=1:lwlo=on:nwc=10.0:sp=weighted_frequency:urr=on:i=3443:si=on:rtra=on_0");
   quick.push("dis+10_16:1_avsq=on:avsqr=1,16:fd=preordered:sgt=8:sos=all:ss=axioms:to=lpo:i=1288:si=on:rtra=on_0");
   quick.push("dis+10_1:1_s2a=on:sp=occurrence:to=lpo:i=293:si=on:rtra=on_0");
   quick.push("lrs+1010_1:6_anc=all:awrs=decay:bs=on:erd=off:ins=1:sd=1:sgt=16:sos=all:spb=goal:ss=axioms:st=1.5:to=lpo:i=1221:si=on:rtra=on_0");
   quick.push("ott+1666_5:1_aac=none:bs=unit_only:kws=inv_frequency:nwc=5.0:rawr=on:s2a=on:s2agt=64:sac=on:sp=occurrence:spb=goal:urr=on:i=13536:si=on:rtra=on_0");
  // Improves by expected 77.33427083754582 probs costing 239991 Mi
  // Sub-schedule for 480000Mi strat cap / 480000Mi overall limit
   quick.push("lrs+1011_8:1_cond=fast:drc=off:nwc=3.0:rawr=on:s2a=on:sac=on:slsq=on:slsqr=40,243:sp=const_frequency:to=lpo:uhcvi=on:i=8121:si=on:rtra=on_0");
   quick.push("dis+1011_2:1_acc=on:br=off:drc=off:kws=precedence:newcnf=on:sp=reverse_arity:tgt=ground:uhcvi=on:i=13525:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_bd=off:sos=all:ss=axioms:i=3630:si=on:rtra=on_0");
   quick.push("dis+21_1:4_bs=unit_only:bsd=on:ile=on:sp=const_min:tgt=full:to=lpo:uhcvi=on:i=2762:si=on:rtra=on_0");
   quick.push("lrs+10_7:4_acc=on:drc=off:kws=inv_frequency:nm=16:sp=weighted_frequency:spb=intro:ss=axioms:tgt=full:i=3049:si=on:rtra=on_0");
   quick.push("ott+21_1:1_av=off:nwc=5.0:s2a=on:spb=intro:to=lpo:i=1038:si=on:rtra=on_0");
   quick.push("lrs+1011_3:2_lsd=30:nm=30:s2a=on:s2agt=15:slsq=on:spb=goal:to=lpo:i=1401:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_bd=off:fsr=off:lecc=0.5:lsd=50:nm=2:s2a=on:s2at=3.0:sp=frequency:tgt=ground:i=3853:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_avsq=on:bce=on:fde=unused:ins=2:kws=inv_frequency:sos=on:sp=reverse_arity:urr=on:i=3073:si=on:rtra=on_0");
   quick.push("ott+2_1:1_lcm=predicate:s2a=on:s2agt=4:s2at=2.0:urr=on:i=6097:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_bs=on:fde=unused:flr=on:s2a=on:s2at=2.0:i=1860:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_ep=RS:ss=axioms:i=1165:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_fde=unused:uhcvi=on:i=16232:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_bd=off:fde=none:newcnf=on:nwc=5.0:i=4876:si=on:rtra=on_0");
   quick.push("lrs+1011_3:1_nm=2:s2a=on:s2at=3.0:sp=const_min:ss=axioms:st=5.0:tgt=full:i=1673:si=on:rtra=on_0");
   quick.push("ott+10_1:1_av=off:erd=off:sos=on:ss=axioms:st=1.5:urr=on:i=10207:si=on:rtra=on_0");
   quick.push("ott+21_314:127_av=off:bd=preordered:drc=off:fde=none:gsp=on:nm=6:s2a=on:s2agt=30:sp=const_min:spb=goal:urr=ec_only:i=1565:si=on:rtra=on_0");
   quick.push("dis+1011_7:3_aac=none:bsr=unit_only:er=filter:kws=precedence:lma=on:nm=0:sd=2:sgt=16:sp=unary_first:ss=axioms:tgt=ground:i=920:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_ins=2:kws=precedence:nwc=5.0:sac=on:urr=ec_only:i=2425:si=on:rtra=on_0");
   quick.push("ott+21_11537325:1048576_awrs=decay:awrsf=30:bd=off:nm=20:nwc=10.0:sd=10:sp=weighted_frequency:ss=axioms:st=2.0:urr=on:i=3718:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_ins=2:nm=2:sp=frequency:tgt=ground:to=lpo:i=5996:si=on:rtra=on_0");
   quick.push("ott+21_1:1_kws=precedence:nm=4:sos=on:sp=frequency:uhcvi=on:updr=off:urr=on:i=5264:si=on:rtra=on_0");
   quick.push("dis+1010_1:1024_bd=off:drc=off:newcnf=on:rawr=on:s2pl=on:sd=2:sgt=20:sp=const_frequency:spb=goal_then_units:ss=axioms:tgt=full:i=3581:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_drc=off:newcnf=on:nm=2:sd=1:sp=occurrence:ss=axioms:st=3.0:i=4038:si=on:rtra=on_0");
   quick.push("dis+21_2:3_cond=on:fde=none:lcm=reverse:nm=0:plsq=on:plsqc=1:plsqr=32,1:sac=on:spb=goal_then_units:tgt=full:i=14261:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_avsq=on:avsqr=1,2:bd=off:kws=inv_frequency:nm=6:sos=all:spb=intro:i=7339:si=on:rtra=on_0");
   quick.push("dis+1011_1:7_av=off:bsd=on:drc=off:fd=preordered:ins=3:lsd=60:nm=2:nwc=10.0:sp=const_min:ss=axioms:st=3.0:i=5995:si=on:rtra=on_0");
   quick.push("dis+10_1:1_s2a=on:s2agt=16:i=1362:si=on:rtra=on_0");
   quick.push("lrs+10_1:128_acc=on:awrs=decay:awrsf=30:fd=preordered:fde=none:ins=3:kws=arity_squared:newcnf=on:nwc=5.0:rnwc=on:s2a=on:sp=unary_frequency:ss=axioms:i=1394:si=on:rtra=on_0");
   quick.push("dis-1011_1:128_bd=off:drc=off:fsd=on:sp=const_frequency:ss=axioms:tgt=ground:i=4809:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_cond=on:nwc=10.0:ss=axioms:st=2.0:urr=on:i=3544:si=on:rtra=on_0");
   quick.push("dis+10_8:1_av=off:ep=R:plsq=on:plsqr=204383,524288:sos=all:i=9186:si=on:rtra=on_0");
   quick.push("dis-1010_1:1_avsq=on:avsqc=3:avsqr=1,16:flr=on:nwc=10.0:s2a=on:s2agt=32:sp=frequency:spb=goal_then_units:tgt=ground:i=8899:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_amm=off:sgt=8:sos=all:sp=unary_first:ss=axioms:to=lpo:i=1339:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_afr=on:kws=precedence:nm=16:sp=weighted_frequency:spb=goal_then_units:ss=axioms:tgt=ground:i=3722:si=on:rtra=on_0");
   quick.push("dis+0_16:1_br=off:kws=inv_frequency:s2a=on:s2at=5.0:urr=on:i=2417:si=on:rtra=on_0");
   quick.push("dis-1011_1:28_av=off:drc=off:fde=unused:s2a=on:tgt=full:i=3375:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_avsq=on:drc=off:ins=1:rawr=on:spb=non_intro:ss=axioms:st=2.0:tgt=ground:urr=on:i=1807:si=on:rtra=on_0");
   quick.push("ott+2_1:1_bsr=unit_only:flr=on:sac=on:sos=all:i=3511:si=on:rtra=on_0");
   quick.push("dis+10_1:1_s2agt=16:slsq=on:slsqc=1:sp=weighted_frequency:to=lpo:i=410:si=on:rtra=on_0");
   quick.push("lrs+10_4:1_av=off:sd=2:sos=on:ss=axioms:urr=on:i=14864:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_anc=none:ep=RS:nm=2:sd=10:sgt=10:sp=const_max:ss=axioms:i=971:si=on:rtra=on_0");
   quick.push("dis+11_1:3_avsq=on:avsql=on:bd=off:drc=off:fd=preordered:kws=inv_frequency:lma=on:newcnf=on:sp=reverse_frequency:tgt=ground:uhcvi=on:i=10010:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_gsp=on:kws=arity:plsq=on:plsqr=1,1:s2a=on:s2at=2.0:sp=unary_frequency:spb=goal_then_units:i=9429:si=on:rtra=on_0");
   quick.push("dis+1011_1:4_avsq=on:bd=off:kws=inv_frequency:nwc=5.0:s2a=on:sac=on:sp=const_frequency:i=1629:si=on:rtra=on_0");
   quick.push("ott+1002_16:1_add=off:anc=all_dependent:nm=64:sac=on:slsq=on:slsqr=1,16:urr=on:i=6961:si=on:rtra=on_0");
   quick.push("lrs+1010_1:3_av=off:drc=off:foolp=on:kws=arity_squared:nm=20:nwc=10.0:plsq=on:plsqc=1:plsqr=32,1:sp=unary_frequency:tgt=full:i=7727:si=on:rtra=on_0");
   quick.push("dis+1011_8:1_avsq=on:ep=RS:fsr=off:plsq=on:plsqr=32,1:ss=axioms:st=1.5:i=720:si=on:rtra=on_0");
   quick.push("ott+21_1:1_bsr=unit_only:fsr=off:kws=inv_arity:nwc=10.0:rawr=on:sos=all:sp=frequency:i=1566:si=on:rtra=on_0");
   quick.push("lrs+21_1:7_drc=off:gsp=on:sd=1:sgt=64:ss=axioms:urr=on:i=3830:si=on:rtra=on_0");
   quick.push("lrs+10_1:5_av=off:drc=off:gsp=on:kws=precedence:s2a=on:s2at=-1.0:sos=on:spb=goal_then_units:i=5072:si=on:rtra=on_0");
   quick.push("dis-1011_1:4_av=off:drc=off:fde=unused:kws=inv_frequency:nm=32:nwc=2.0:tgt=full:i=31202:si=on:rtra=on_0");
   quick.push("lrs+1011_1:12_amm=off:br=off:ins=1:s2a=on:s2at=5.0:sims=off:urr=on:i=15694:si=on:rtra=on_0");
   quick.push("ott+21_35:3_drc=off:s2at=5.0:sac=on:slsq=on:slsqr=1,8:sp=reverse_frequency:ss=axioms:urr=on:i=26662:si=on:rtra=on_0");
   quick.push("lrs+2_1:4_er=filter:plsq=on:plsqc=1:plsqr=32,1:sp=frequency:spb=goal:ss=axioms:st=2.0:tgt=ground:urr=on:i=1189:si=on:rtra=on_0");
   quick.push("ott-10_8:1_flr=on:rawr=on:s2a=on:s2at=5.0:sac=on:slsq=on:i=9607:si=on:rtra=on_0");
   quick.push("lrs+10_4:1_bd=preordered:nwc=5.0:sd=1:ss=axioms:urr=on:i=2880:si=on:rtra=on_0");
   quick.push("lrs+1011_1:14_av=off:drc=off:kws=frequency:lecc=1.5:lwlo=on:s2a=on:s2at=5.0:slsq=on:slsql=off:slsqr=3,4:spb=goal:tgt=full:i=16083:si=on:rtra=on_0");
   quick.push("ott+10_1:1_s2a=on:s2agt=16:sgt=10:slsq=on:slsqc=1:sp=const_min:spb=goal_then_units:ss=axioms:to=lpo:i=2785:si=on:rtra=on_0");
   quick.push("ott+10_1:1_flr=on:fsr=off:nwc=10.0:s2a=on:sac=on:spb=goal:urr=on:i=3506:si=on:rtra=on_0");
   quick.push("dis+1011_1:16_drc=off:sac=on:spb=goal_then_units:ss=axioms:st=5.0:i=10538:si=on:rtra=on_0");
   quick.push("dis+1010_8:1_fde=none:kws=frequency:newcnf=on:s2a=on:s2agt=64:sac=on:slsq=on:slsqr=1,2:i=6707:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_aac=none:ep=RST:s2a=on:sos=all:sp=occurrence:spb=goal_then_units:i=17627:si=on:rtra=on_0");
   quick.push("lrs+1011_1:2_ins=1:newcnf=on:spb=goal:ss=axioms:tgt=full:i=22096:si=on:rtra=on_0");
   quick.push("dis+1011_3:1_av=off:fsr=off:nwc=10.0:sgt=16:sp=unary_first:ss=axioms:st=2.0:i=1406:si=on:rtra=on_0");
   quick.push("ott+1004_1:12_atotf=0.2:ins=1:sd=1:sgt=32:sp=frequency:ss=axioms:st=3.0:tgt=full:i=11080:si=on:rtra=on_0");
   quick.push("lrs+1002_16:1_flr=on:nwc=3.0:s2a=on:s2agt=16:sp=const_min:spb=goal:to=lpo:urr=on:i=1399:si=on:rtra=on_0");
   quick.push("lrs-1011_1:20_sd=2:sgt=30:sp=frequency:spb=goal_then_units:ss=axioms:tgt=full:i=1428:si=on:rtra=on_0");
   quick.push("dis+1002_1:1_av=off:cond=fast:gs=on:ins=3:sos=all:sp=frequency:to=lpo:i=1092:si=on:rtra=on_0");
   quick.push("dis-1011_1:1_atotf=0.1:drc=off:kws=inv_precedence:s2a=on:s2agt=20:sac=on:spb=non_intro:tgt=ground:i=11373:si=on:rtra=on_0");
   quick.push("dis-1011_1:14_av=off:awrs=decay:awrsf=200:ins=1:nwc=10.0:sos=on:sp=unary_first:i=4014:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_bd=off:ins=1:lwlo=on:nwc=10.0:sp=weighted_frequency:urr=on:i=3443:si=on:rtra=on_0");
   quick.push("dis+10_16:1_avsq=on:avsqr=1,16:fd=preordered:sgt=8:sos=all:ss=axioms:to=lpo:i=1776:si=on:rtra=on_0");
   quick.push("lrs+1002_3:1_plsq=on:plsqr=1,2:s2a=on:s2agt=8:sac=on:sgt=4:ss=axioms:i=882:si=on:rtra=on_0");
   quick.push("lrs+1010_1:6_anc=all:awrs=decay:bs=on:erd=off:ins=1:sd=1:sgt=16:sos=all:spb=goal:ss=axioms:st=1.5:to=lpo:i=1221:si=on:rtra=on_0");
   quick.push("dis+10_4:1_bd=off:drc=off:kws=precedence:nm=2:rawr=on:s2a=on:slsq=on:slsqc=3:slsql=off:slsqr=1,8:sp=const_frequency:urr=ec_only:i=8538:si=on:rtra=on_0");
   quick.push("dis+2_875:524288_av=off:erd=off:kws=inv_arity_squared:rawr=on:sos=all:spb=goal_then_units:ss=axioms:st=3.0:i=2088:si=on:rtra=on_0");
   quick.push("dis+2_3:1_awrs=converge:awrsf=200:s2a=on:s2at=4.0:uhcvi=on:urr=on:i=16763:si=on:rtra=on_0");
  // Improves by expected 41.86702006570085 probs costing 479219 Mi
  // Sub-schedule for 960000Mi strat cap / 960000Mi overall limit
   quick.push("lrs+1011_8:1_cond=fast:drc=off:nwc=3.0:rawr=on:s2a=on:sac=on:slsq=on:slsqr=40,243:sp=const_frequency:to=lpo:uhcvi=on:i=8121:si=on:rtra=on_0");
   quick.push("dis+1011_2:1_acc=on:br=off:drc=off:kws=precedence:newcnf=on:sp=reverse_arity:tgt=ground:uhcvi=on:i=13525:si=on:rtra=on_0");
   quick.push("dis+1011_1:3_av=off:bsd=on:kws=inv_arity_squared:plsq=on:plsqr=1,8:ss=axioms:tgt=full:i=58470:si=on:rtra=on_0");
   quick.push("lrs+1011_1:24_atotf=0.2:bd=off:s2a=on:s2agt=60:sgt=20:ss=axioms:tgt=ground:i=8120:si=on:rtra=on_0");
   quick.push("ott+1010_8:1_bsr=unit_only:drc=off:fsr=off:plsq=on:plsqc=1:plsqr=32,1:s2a=on:s2agt=32:urr=on:i=6913:si=on:rtra=on_0");
   quick.push("ott+1002_1:1_avsq=on:bce=on:fde=unused:ins=2:kws=inv_frequency:sos=on:sp=reverse_arity:urr=on:i=3073:si=on:rtra=on_0");
   quick.push("lrs+10_1:20_av=off:nm=2:sp=const_frequency:tgt=ground:i=30341:si=on:rtra=on_0");
   quick.push("ott+2_1:1_lcm=predicate:s2a=on:s2agt=4:s2at=2.0:urr=on:i=6322:si=on:rtra=on_0");
   quick.push("lrs+1011_16:1_awrs=converge:lwlo=on:nwc=3.0:s2a=on:s2agt=32:sd=1:sp=const_frequency:ss=axioms:st=3.0:i=7195:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_bd=off:fde=none:newcnf=on:nwc=5.0:i=4876:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_amm=off:bs=unit_only:fd=preordered:kws=inv_frequency:lcm=predicate:newcnf=on:spb=goal:tgt=ground:i=11656:si=on:rtra=on_0");
   quick.push("ott+10_1:1_av=off:erd=off:sos=on:ss=axioms:st=1.5:urr=on:i=10207:si=on:rtra=on_0");
   quick.push("ott+2_4:1_br=off:bsd=on:drc=off:nm=2:sp=unary_first:urr=on:i=16933:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_anc=none:flr=on:kws=inv_arity:nm=0:nwc=5.0:sd=1:sgt=60:spb=units:ss=axioms:uhcvi=on:i=3056:si=on:rtra=on_0");
   quick.push("dis+1010_1:1_ins=2:nm=2:sp=frequency:tgt=ground:to=lpo:i=5996:si=on:rtra=on_0");
   quick.push("lrs+10_5:1_br=off:s2a=on:s2at=5.0:sd=2:ss=axioms:st=2.0:urr=on:i=3173:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_drc=off:newcnf=on:nm=2:sd=1:sp=occurrence:ss=axioms:st=3.0:i=4038:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_avsq=on:avsqr=1,2:bd=off:kws=inv_frequency:nm=6:sos=all:spb=intro:i=8587:si=on:rtra=on_0");
   quick.push("dis+1011_1:7_av=off:bsd=on:drc=off:fd=preordered:ins=3:lsd=60:nm=2:nwc=10.0:sp=const_min:ss=axioms:st=3.0:i=5995:si=on:rtra=on_0");
   quick.push("lrs-1011_1:32_av=off:bsd=on:drc=off:nm=10:sd=2:sgt=20:ss=axioms:st=1.5:tgt=ground:i=11353:si=on:rtra=on_0");
   quick.push("lrs+10_1:1_drc=off:erd=off:flr=on:sp=frequency:ss=axioms:to=lpo:i=3413:si=on:rtra=on_0");
   quick.push("dis-1011_1:128_bd=off:drc=off:fsd=on:sp=const_frequency:ss=axioms:tgt=ground:i=4809:si=on:rtra=on_0");
   quick.push("lrs+1002_1:1_bd=preordered:fd=preordered:fsd=on:newcnf=on:plsq=on:plsql=on:slsq=on:sos=on:sp=weighted_frequency:spb=goal:to=lpo:i=4793:si=on:rtra=on_0");
   quick.push("dis+1011_1:3_atotf=0.1:flr=on:kws=precedence:sp=const_min:i=35258:si=on:rtra=on_0");
   quick.push("dis-1010_1:1_avsq=on:avsqc=3:avsqr=1,16:flr=on:nwc=10.0:s2a=on:s2agt=32:sp=frequency:spb=goal_then_units:tgt=ground:i=8899:si=on:rtra=on_0");
   quick.push("lrs-10_1:4_acc=model:nm=0:s2a=on:sac=on:sp=reverse_arity:ss=axioms:i=6565:si=on:rtra=on_0");
   quick.push("dis+1011_1:3_lsd=10:sp=const_frequency:ss=axioms:st=2.0:tgt=full:uhcvi=on:i=5521:si=on:rtra=on_0");
   quick.push("dis+21_5:1_acc=on:br=off:lcm=predicate:newcnf=on:nicw=on:nm=2:sp=unary_first:ss=axioms:st=1.5:urr=on:i=5474:si=on:rtra=on_0");
   quick.push("ott+2_1:1_bsr=unit_only:flr=on:sac=on:sos=all:i=5123:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_acc=on:avsq=on:avsqc=5:drc=off:fde=none:kws=precedence:s2a=on:s2at=6.0:sp=frequency:spb=goal:tgt=ground:i=22924:si=on:rtra=on_0");
   quick.push("dis+10_1:1_s2agt=16:slsq=on:slsqc=1:sp=weighted_frequency:to=lpo:i=767:si=on:rtra=on_0");
   quick.push("lrs+10_2:3_av=off:bd=off:br=off:bs=unit_only:drc=off:nwc=5.0:sp=const_min:ss=axioms:tgt=ground:i=40987:si=on:rtra=on_0");
   quick.push("ott+10_8:1_acc=on:fsr=off:kws=frequency:nm=40:nwc=10.0:s2a=on:s2at=1.5:sac=on:tgt=full:urr=on:i=2607:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_gsp=on:kws=arity:plsq=on:plsqr=1,1:s2a=on:s2at=2.0:sp=unary_frequency:spb=goal_then_units:i=9429:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_av=off:drc=off:fde=unused:kws=inv_precedence:s2a=on:s2at=5.0:sp=reverse_arity:spb=goal_then_units:tgt=ground:i=16263:si=on:rtra=on_0");
   quick.push("ott+1002_16:1_add=off:anc=all_dependent:nm=64:sac=on:slsq=on:slsqr=1,16:urr=on:i=3798:si=on:rtra=on_0");
   quick.push("ott+21_1:1_bsr=unit_only:fsr=off:kws=inv_arity:nwc=10.0:rawr=on:sos=all:sp=frequency:i=1566:si=on:rtra=on_0");
   quick.push("lrs+21_1:7_drc=off:gsp=on:sd=1:sgt=64:ss=axioms:urr=on:i=3830:si=on:rtra=on_0");
   quick.push("dis-1011_1:4_av=off:drc=off:fde=unused:kws=inv_frequency:nm=32:nwc=2.0:tgt=full:i=172628:si=on:rtra=on_0");
   quick.push("ott+21_35:3_drc=off:s2at=5.0:sac=on:slsq=on:slsqr=1,8:sp=reverse_frequency:ss=axioms:urr=on:i=23269:si=on:rtra=on_0");
   quick.push("ott-10_8:1_flr=on:rawr=on:s2a=on:s2at=5.0:sac=on:slsq=on:i=9607:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_ep=RS:fde=unused:slsq=on:slsqr=1,2:sp=occurrence:spb=goal:i=5156:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_bd=off:drc=off:kws=inv_frequency:s2a=on:slsq=on:slsqr=1,16:sp=reverse_frequency:i=15582:si=on:rtra=on_0");
   quick.push("ott+10_1:1_flr=on:fsr=off:nwc=10.0:s2a=on:sac=on:spb=goal:urr=on:i=1480:si=on:rtra=on_0");
   quick.push("dis+1011_1:16_drc=off:sac=on:spb=goal_then_units:ss=axioms:st=5.0:i=30462:si=on:rtra=on_0");
   quick.push("dis+1010_8:1_fde=none:kws=frequency:newcnf=on:s2a=on:s2agt=64:sac=on:slsq=on:slsqr=1,2:i=58288:si=on:rtra=on_0");
   quick.push("ott+10_5:1_newcnf=on:nm=16:sp=frequency:spb=goal:tgt=full:urr=on:i=23110:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_aac=none:ep=RST:s2a=on:sos=all:sp=occurrence:spb=goal_then_units:i=66939:si=on:rtra=on_0");
   quick.push("lrs+1011_1:2_ins=1:newcnf=on:spb=goal:ss=axioms:tgt=full:i=22096:si=on:rtra=on_0");
   quick.push("ott+1004_1:12_atotf=0.2:ins=1:sd=1:sgt=32:sp=frequency:ss=axioms:st=3.0:tgt=full:i=11080:si=on:rtra=on_0");
   quick.push("dis+10_1:1_drc=off:nm=2:nwc=3.0:sp=const_frequency:spb=non_intro:urr=on:i=12548:si=on:rtra=on_0");
   quick.push("dis-1011_1:1_atotf=0.1:drc=off:kws=inv_precedence:s2a=on:s2agt=20:sac=on:spb=non_intro:tgt=ground:i=56532:si=on:rtra=on_0");
   quick.push("dis-1011_1:14_av=off:awrs=decay:awrsf=200:ins=1:nwc=10.0:sos=on:sp=unary_first:i=3771:si=on:rtra=on_0");
   quick.push("lrs+1011_4:1_afr=on:rawr=on:slsq=on:slsqr=1,2:sp=const_max:spb=intro:uhcvi=on:urr=ec_only:i=27814:si=on:rtra=on_0");
   quick.push("dis+2_875:524288_av=off:erd=off:kws=inv_arity_squared:rawr=on:sos=all:spb=goal_then_units:ss=axioms:st=3.0:i=2088:si=on:rtra=on_0");
  // Improves by expected 18.1183416852127 probs costing 952371 Mi
  // Sub-schedule for 960000Mi strat cap / 960000Mi overall limit
   quick.push("lrs+1011_1:8_av=off:sd=1:spb=goal_then_units:ss=axioms:st=5.0:uhcvi=on:i=80949:si=on:rtra=on_0");
   quick.push("dis+1011_1:3_av=off:bsd=on:kws=inv_arity_squared:plsq=on:plsqr=1,8:ss=axioms:tgt=full:i=47349:si=on:rtra=on_0");
   quick.push("ott+1010_8:1_bsr=unit_only:drc=off:fsr=off:plsq=on:plsqc=1:plsqr=32,1:s2a=on:s2agt=32:urr=on:i=6913:si=on:rtra=on_0");
   quick.push("ott+2_1:1_lcm=predicate:s2a=on:s2agt=4:s2at=2.0:urr=on:i=3807:si=on:rtra=on_0");
   quick.push("lrs+1011_16:1_awrs=converge:lwlo=on:nwc=3.0:s2a=on:s2agt=32:sd=1:sp=const_frequency:ss=axioms:st=3.0:i=25600:si=on:rtra=on_0");
   quick.push("dis+1010_1:24_kws=arity_squared:sac=on:sgt=20:sp=unary_frequency:ss=axioms:tgt=full:i=52880:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_bd=off:fde=none:newcnf=on:nwc=5.0:i=4876:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_amm=off:bs=unit_only:fd=preordered:kws=inv_frequency:lcm=predicate:newcnf=on:spb=goal:tgt=ground:i=83426:si=on:rtra=on_0");
   quick.push("lrs+1010_1:16_av=off:s2a=on:sp=const_frequency:tgt=full:i=26935:si=on:rtra=on_0");
   quick.push("dis-1011_1:128_bd=off:drc=off:fsd=on:sp=const_frequency:ss=axioms:tgt=ground:i=4809:si=on:rtra=on_0");
   quick.push("dis+1011_1:3_atotf=0.1:flr=on:kws=precedence:sp=const_min:i=35258:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_acc=on:avsq=on:avsqc=5:drc=off:fde=none:kws=precedence:s2a=on:s2at=6.0:sp=frequency:spb=goal:tgt=ground:i=22924:si=on:rtra=on_0");
   quick.push("lrs+10_2:3_av=off:bd=off:br=off:bs=unit_only:drc=off:nwc=5.0:sp=const_min:ss=axioms:tgt=ground:i=27187:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_av=off:drc=off:fde=unused:kws=inv_precedence:s2a=on:s2at=5.0:sp=reverse_arity:spb=goal_then_units:tgt=ground:i=16263:si=on:rtra=on_0");
   quick.push("lrs+1011_1:12_amm=off:br=off:ins=1:s2a=on:s2at=5.0:sims=off:urr=on:i=25881:si=on:rtra=on_0");
   quick.push("ott+21_35:3_drc=off:s2at=5.0:sac=on:slsq=on:slsqr=1,8:sp=reverse_frequency:ss=axioms:urr=on:i=26662:si=on:rtra=on_0");
   quick.push("ott-10_8:1_flr=on:rawr=on:s2a=on:s2at=5.0:sac=on:slsq=on:i=9607:si=on:rtra=on_0");
   quick.push("lrs+10_1:2_av=off:br=off:drc=off:lecc=1.6:sp=weighted_frequency:tgt=full:i=179211:si=on:rtra=on_0");
   quick.push("lrs+1011_1:14_av=off:drc=off:kws=frequency:lecc=1.5:lwlo=on:s2a=on:s2at=5.0:slsq=on:slsql=off:slsqr=3,4:spb=goal:tgt=full:i=22579:si=on:rtra=on_0");
   quick.push("ott+10_1:1_flr=on:fsr=off:nwc=10.0:s2a=on:sac=on:spb=goal:urr=on:i=3506:si=on:rtra=on_0");
   quick.push("dis+1011_1:16_drc=off:sac=on:spb=goal_then_units:ss=axioms:st=5.0:i=30462:si=on:rtra=on_0");
   quick.push("dis+1010_8:1_fde=none:kws=frequency:newcnf=on:s2a=on:s2agt=64:sac=on:slsq=on:slsqr=1,2:i=54338:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_aac=none:ep=RST:s2a=on:sos=all:sp=occurrence:spb=goal_then_units:i=66939:si=on:rtra=on_0");
   quick.push("dis+2_875:524288_av=off:erd=off:kws=inv_arity_squared:rawr=on:sos=all:spb=goal_then_units:ss=axioms:st=3.0:i=2088:si=on:rtra=on_0");
   quick.push("ott+1011_1:10_nwc=10.0:ss=axioms:tgt=full:i=36675:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_av=off:bd=off:lwlo=on:nwc=10.0:sp=unary_first:to=lpo:i=60909:si=on:rtra=on_0");
  // Improves by expected 5.968501703193174 probs costing 958007 Mi
  // Sub-schedule for 960000Mi strat cap / 960000Mi overall limit
   quick.push("dis+1011_1:3_av=off:bsd=on:kws=inv_arity_squared:plsq=on:plsqr=1,8:ss=axioms:tgt=full:i=47349:si=on:rtra=on_0");
   quick.push("ott+1010_8:1_bsr=unit_only:drc=off:fsr=off:plsq=on:plsqc=1:plsqr=32,1:s2a=on:s2agt=32:urr=on:i=6913:si=on:rtra=on_0");
   quick.push("ott+2_1:1_lcm=predicate:s2a=on:s2agt=4:s2at=2.0:urr=on:i=6097:si=on:rtra=on_0");
   quick.push("lrs+1010_1:1_bd=off:fde=none:newcnf=on:nwc=5.0:i=4876:si=on:rtra=on_0");
   quick.push("ott+10_1:1_bd=off:nm=30:slsq=on:slsqr=1,2:sp=unary_first:ss=axioms:st=2.0:uhcvi=on:urr=on:i=52916:si=on:rtra=on_0");
   quick.push("dis+1011_1:3_atotf=0.1:flr=on:kws=precedence:sp=const_min:i=25809:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_acc=on:avsq=on:avsqc=5:drc=off:fde=none:kws=precedence:s2a=on:s2at=6.0:sp=frequency:spb=goal:tgt=ground:i=22924:si=on:rtra=on_0");
   quick.push("dis+10_1:14_acc=on:drc=off:fd=preordered:fde=unused:plsq=on:plsqr=1,32:sac=on:sp=occurrence:tgt=full:i=196386:si=on:rtra=on_0");
   quick.push("lrs+1011_1:1_av=off:drc=off:fde=unused:kws=inv_precedence:s2a=on:s2at=5.0:sp=reverse_arity:spb=goal_then_units:tgt=ground:i=16263:si=on:rtra=on_0");
   quick.push("dis+1011_1:1_ep=RS:fde=unused:slsq=on:slsqr=1,2:sp=occurrence:spb=goal:i=122892:si=on:rtra=on_0");
   quick.push("lrs+10_1:2_av=off:br=off:drc=off:lecc=1.6:sp=weighted_frequency:tgt=full:i=193646:si=on:rtra=on_0");
   quick.push("ott+10_1:1_flr=on:fsr=off:nwc=10.0:s2a=on:sac=on:spb=goal:urr=on:i=3506:si=on:rtra=on_0");
   quick.push("dis+1011_1:16_drc=off:sac=on:spb=goal_then_units:ss=axioms:st=5.0:i=30462:si=on:rtra=on_0");
   quick.push("dis+1010_8:1_fde=none:kws=frequency:newcnf=on:s2a=on:s2agt=64:sac=on:slsq=on:slsqr=1,2:i=54338:si=on:rtra=on_0");
   quick.push("lrs+21_1:1_acc=on:atotf=0.1:drc=off:gs=on:lwlo=on:sac=on:sp=const_frequency:ss=axioms:tgt=full:i=77167:si=on:rtra=on_0");
   quick.push("dis+2_875:524288_av=off:erd=off:kws=inv_arity_squared:rawr=on:sos=all:spb=goal_then_units:ss=axioms:st=3.0:i=2088:si=on:rtra=on_0");
   quick.push("ott+1011_1:10_nwc=10.0:ss=axioms:tgt=full:i=79160:si=on:rtra=on_0");
  // Improves by expected 2.9329672676943623 probs costing 942775 Mi
  // Overall score 6292.973951117842 probs on average / budget 3812207 Mi
  }
}

#endif
