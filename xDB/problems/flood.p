% XDB problem
% Name an OECD country's capital that is at the same latitude as Moscow (to the nearest degree), that could get flooded

%----These come from SUMO
tff(kb_SUMO_28,axiom,(
    ! [V__X,V__Y,V__Z] :
      ( ( s__instance(V__Y,s__SetOrClass)
        & s__instance(V__X,s__SetOrClass) )
     => ( ( s__subclass(V__X,V__Y)
          & s__instance(V__Z,V__X) )
       => s__instance(V__Z,V__Y) ) ) )).

tff(kb_SUMO_MILO_6297,axiom,(
    s__instance(s__WaterArea,s__SetOrClass) )).

tff(kb_SUMO_MILO_10029,axiom,(
    s__instance(s__BodyOfWater,s__SetOrClass) )).

tff(kb_SUMO_MILO_DOMAINS_9645,axiom,(
    s__subclass(s__Sea,s__BodyOfWater) )).

tff(kb_SUMO_MILO_DOMAINS_9546,axiom,(
    s__subclass(s__BodyOfWater,s__WaterArea) )).

tff(kb_SUMO_MILO_DOMAINS_80407,axiom,(
    s__instance(s__Sea,s__SetOrClass) )).

%----These are supplied by Geoff
tff(flood_near_water,axiom,
    ! [W,C] :
      ( ( s__orientation(C,W,s__Near)
        & s__instance(W,s__WaterArea) )
     => s__capability(s__Flooding,s__located__m,C) ) ).

tff(coastal_cities_near_water,axiom,
    ! [City] :
      ( s__instance(City,Coastaly)
     => ? [Sea] :-
          ( s__instance(Sea,s__Sea)
          & s__orientation(City,Sea,s__Near) ) ) ).

tff(where,conjecture,
    ? [City,Country,CityLat,CityLong,CityName,CityCountry,Latitude,
       MoscowLat,MoscowLong,MoscowName,MoscowCountry] :
      ( s__instance(Country,s__sOECDCountry)
      & s__capitalCity(City,Country)
      & $different(City,s__MoscowRussia)
      & s__latitude(City,CityLat)
      & s__longitude(City,CityLong)
      & $evaleq($to_int(CityLat),Latitude)
      & latlong('Moscow',MoscowLat,MoscowLong,MoscowName,MoscowCountry)
      & $evaleq($to_int(MoscowLat),Latitude)
      & s__capability(s__Flooding,s__located__m,City))).
%      & print(printall(nl,nl,'The city is ',City,' in ',Country,
% ' at latitude ',CityLat,' (Moscow is at ',MoscowLat,')',nl,nl)) ) ).