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

using namespace Lib;
using namespace Shell;
using namespace CASC;

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
    // Empirically sorted
    quick.push("lrs+10_1_iik=one:ind=both:sos=theory:sstl=1_89");
    quick.push("dis+1002_1_aac=none:anc=all:ind=both:sos=theory:sac=on:sstl=1:to=lpo_30");
    quick.push("lrs+10_1_iik=one:ind=both:sos=theory:sstl=1:to=lpo_89");
    quick.push("lrs+10_1_drc=off:iik=all:ind=both:to=lpo_89");
    quick.push("lrs+10_1_iik=all:ind=both:to=lpo_89");
    quick.push("lrs+10_1_drc=off:iik=all:ind=both:sos=theory:sstl=1:to=lpo_89");
    quick.push("lrs+10_1_iik=two:ind=both:sos=theory:sstl=1:to=lpo_89");
    quick.push("lrs+10_1_iik=one:ind=both:to=lpo_89");
    quick.push("lrs+10_1_drc=off:iik=one:ind=both:sos=theory:sstl=1:to=lpo_89");
    quick.push("lrs+10_1_av=off:br=off:ind=both:urr=on_89");
    quick.push("lrs+10_1_drc=off:iik=one:ind=both:to=lpo_89");
    quick.push("lrs+10_1_drc=off:iik=all:ind=both_89");
    quick.push("lrs+10_1_drc=off:iik=one:ind=both:sos=theory:sstl=1_89");
    quick.push("lrs+10_1_iik=one:ind=both_89");
    quick.push("lrs+10_1_iik=two:ind=both:to=lpo_89");
    quick.push("lrs+10_1_drc=off:iik=two:ind=both:sos=theory:sstl=1:to=lpo_89");
    // The rest
    quick.push("lrs+10_1_drc=off:iik=one:ind=both_89");
    quick.push("lrs+10_1_iik=all:ind=both:sos=theory:sstl=1:to=lpo_89");
    quick.push("lrs+10_1_drc=off:iik=all:ind=both:sos=theory:sstl=1_89");
    quick.push("lrs+10_1_iik=all:ind=both:sos=theory:sstl=1_89");
    quick.push("lrs+10_1_iik=all:ind=both_89");
    quick.push("lrs+10_1_drc=off:iik=two:ind=both:to=lpo_89");
    quick.push("lrs+10_1_drc=off:iik=two:ind=both:sos=theory:sstl=1_89");
    quick.push("lrs+10_1_drc=off:iik=two:ind=both_89");
    quick.push("lrs+10_1_iik=two:ind=both:sos=theory:sstl=1_89");
    quick.push("lrs+10_1_iik=two:ind=both_89");
    quick.push("lrs+10_1_drc=off:iik=one:ind=both:indoct=on:sos=theory:sstl=1:to=lpo_89");
    quick.push("lrs+10_1_iik=one:ind=both:indoct=on:sos=theory:sstl=1:to=lpo_89");
    quick.push("lrs+10_1_drc=off:iik=one:ind=both:indoct=on:sos=theory:sstl=1_89");
    quick.push("lrs+10_1_iik=one:ind=both:indoct=on:sos=theory:sstl=1_89");
    quick.push("lrs+10_1_drc=off:iik=two:ind=both:indoct=on:sos=theory:sstl=1:to=lpo_89");
    quick.push("lrs+10_1_iik=two:ind=both:indoct=on:sos=theory:sstl=1:to=lpo_89");
    quick.push("lrs+10_1_drc=off:iik=two:ind=both:indoct=on:sos=theory:sstl=1_89");
    quick.push("lrs+10_1_iik=two:ind=both:indoct=on:sos=theory:sstl=1_89");
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
  // Empirically sorted
  quick.push("lrs+10_1_iik=one:ind=int:sos=theory:sstl=1_87");
  quick.push("dis+1002_1_aac=none:anc=all:ind=int:sos=theory:sac=on:sstl=1:to=lpo_30");
  quick.push("lrs+10_1_iik=one:ind=int:sos=theory:sstl=1:to=lpo_87");
  quick.push("lrs+10_1_drc=off:iik=all:ind=int:to=lpo_87");
  quick.push("lrs+10_1_iik=all:ind=int:to=lpo_87");
  quick.push("lrs+10_1_drc=off:iik=all:ind=int:sos=theory:sstl=1:to=lpo_87");
  quick.push("lrs+10_1_iik=two:ind=int:sos=theory:sstl=1:to=lpo_87");
  quick.push("lrs+10_1_iik=one:ind=int:to=lpo_87");
  quick.push("lrs+10_1_drc=off:iik=one:ind=int:sos=theory:sstl=1:to=lpo_87");
  quick.push("lrs+10_1_av=off:br=off:ind=int:urr=on_87");
  quick.push("lrs+10_1_drc=off:iik=one:ind=int:to=lpo_87");
  quick.push("lrs+10_1_drc=off:iik=all:ind=int_87");
  quick.push("lrs+10_1_drc=off:iik=one:ind=int:sos=theory:sstl=1_87");
  quick.push("lrs+10_1_iik=one:ind=int_87");
  quick.push("lrs+10_1_iik=two:ind=int:to=lpo_87");
  quick.push("lrs+10_1_drc=off:iik=two:ind=int:sos=theory:sstl=1:to=lpo_87");
  quick.push("lrs+10_1_avsq=on:drc=off:iik=all:ind=int:to=lpo_30");
  quick.push("lrs+10_1_drc=off:iik=all:ind=int:thsq=on:thsqd=16:to=lpo_30");
  quick.push("lrs+4_5_drc=off:iik=one:ind=int:plsq=on:to=lpo_100");
  // The rest
  quick.push("lrs+10_1_drc=off:iik=one:ind=int_81");
  quick.push("lrs+10_1_iik=all:ind=int:sos=theory:sstl=1:to=lpo_81");
  quick.push("lrs+10_1_drc=off:iik=all:ind=int:sos=theory:sstl=1_81");
  quick.push("lrs+10_1_iik=all:ind=int:sos=theory:sstl=1_81");
  quick.push("lrs+10_1_iik=all:ind=int_81");
  quick.push("lrs+10_1_drc=off:iik=two:ind=int:to=lpo_81");
  quick.push("lrs+10_1_drc=off:iik=two:ind=int:sos=theory:sstl=1_81");
  quick.push("lrs+10_1_drc=off:iik=two:ind=int_81");
  quick.push("lrs+10_1_iik=two:ind=int:sos=theory:sstl=1_81");
  quick.push("lrs+10_1_iik=two:ind=int_81");
  quick.push("lrs+10_1_drc=off:iik=one:ind=int:indoct=on:sos=theory:sstl=1:to=lpo_81");
  quick.push("lrs+10_1_iik=one:ind=int:indoct=on:sos=theory:sstl=1:to=lpo_81");
  quick.push("lrs+10_1_iik=one:drc=off:ind=int:indoct=on:sos=theory:sstl=1_81");
  quick.push("lrs+10_1_iik=one:ind=int:indoct=on:sos=theory:sstl=1_81");
  quick.push("lrs+10_1_drc=off:iik=two:ind=int:indoct=on:sos=theory:sstl=1:to=lpo_81");
  quick.push("lrs+10_1_iik=two:ind=int:indoct=on:sos=theory:sstl=1:to=lpo_81");
  quick.push("lrs+10_1_iik=two:drc=off:ind=int:indoct=on:sos=theory:sstl=1_81");
  quick.push("lrs+10_1_iik=two:ind=int:indoct=on:sos=theory:sstl=1_81");

  fallback.push("lrs+10_1__50");
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
