%------------------------------------------------------------------------------
% File     : HWV087_2 : TPTP v9.0.0. Bugfixed v6.2.0.
% Domain   : Hardware Verification
% Problem  : dmu_dmc property 3 cone of influence 5_b20
% Version  : Especial.
% English  : Verification of a property of the SPARCT2 RTL hardware design.

% Refs     : [Kha14] Khasidashvili (2014), Email to Geoff Sutcliffe
% Source   : [Kha14]
% Names    : dmu_dmc_prop3_cone5_b20 [Kha14]

% Status   : Theorem
% Rating   : 0.62 v9.0.0, 0.50 v8.2.0, 0.62 v7.5.0, 0.70 v7.4.0, 0.62 v7.3.0, 0.50 v7.0.0, 0.57 v6.4.0, 0.33 v6.3.0, 0.71 v6.2.0
% Syntax   : Number of formulae    : 1777 ( 238 unt; 672 typ;   0 def)
%            Number of atoms       : 3682 (  21 equ)
%            Maximal formula atoms :  248 (   2 avg)
%            Number of connectives : 3051 ( 474   ~; 124   |; 731   &)
%                                         (1407 <=>; 315  =>;   0  <=;   0 <~>)
%            Maximal formula depth :  128 (   4 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number arithmetic     : 2138 ( 196 atm;   0 fun;1844 num;  98 var)
%            Number of types       :    3 (   1 usr;   1 ari)
%            Number of type conns  :  773 ( 649   >; 124   *;   0   +;   0  <<)
%            Number of predicates  :  654 ( 650 usr;   3 prp; 0-2 aty)
%            Number of functors    :  399 (  21 usr; 399 con; 0-0 aty)
%            Number of variables   : 1023 (1023   !;   0   ?;1023   :)
% SPC      : TF0_THM_EQU_ARI

% Comments : Copyright 2013 Moshe Emmer and Zurab Khasidashvili
%            Licensed under the Apache License, Version 2.0 (the "License");
%            you may not use this file except in compliance with the License.
%            You may obtain a copy of the License at
%                http://www.apache.org/licenses/LICENSE-2.0
%            Unless required by applicable law or agreed to in writing,
%            software distributed under the License is distributed on an "AS
%            IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
%            express or implied. See the License for the specific language
%            governing permissions and limitations under the License.
% Bugfixes : v6.2.0 - Fixed type declarations.
%------------------------------------------------------------------------------
tff(state_type,type,
    state_type: $tType ).

tff(v16_type,type,
    v16: state_type > $o ).

tff(v14_type,type,
    v14: state_type > $o ).

tff(v10_type,type,
    v10: state_type > $o ).

tff(v42_type,type,
    v42: ( state_type * $int ) > $o ).

tff(v40_type,type,
    v40: ( state_type * $int ) > $o ).

tff(v12_type,type,
    v12: state_type > $o ).

tff(v27_type,type,
    v27: state_type > $o ).

tff(v8_type,type,
    v8: state_type > $o ).

tff(constB0_type,type,
    constB0: state_type ).

tff(constB1_type,type,
    constB1: state_type ).

tff(constB2_type,type,
    constB2: state_type ).

tff(constB3_type,type,
    constB3: state_type ).

tff(constB4_type,type,
    constB4: state_type ).

tff(constB5_type,type,
    constB5: state_type ).

tff(constB6_type,type,
    constB6: state_type ).

tff(constB7_type,type,
    constB7: state_type ).

tff(constB8_type,type,
    constB8: state_type ).

tff(constB9_type,type,
    constB9: state_type ).

tff(constB10_type,type,
    constB10: state_type ).

tff(constB11_type,type,
    constB11: state_type ).

tff(constB12_type,type,
    constB12: state_type ).

tff(constB13_type,type,
    constB13: state_type ).

tff(constB14_type,type,
    constB14: state_type ).

tff(constB15_type,type,
    constB15: state_type ).

tff(constB16_type,type,
    constB16: state_type ).

tff(constB17_type,type,
    constB17: state_type ).

tff(constB18_type,type,
    constB18: state_type ).

tff(constB19_type,type,
    constB19: state_type ).

tff(constB20_type,type,
    constB20: state_type ).

tff(pred_def_9,type,
    v38: ( state_type * $int ) > $o ).

tff(pred_def_10,type,
    v36: ( state_type * $int ) > $o ).

tff(pred_def_11,type,
    v48: state_type > $o ).

tff(pred_def_12,type,
    v50: state_type > $o ).

tff(pred_def_13,type,
    v46: state_type > $o ).

tff(pred_def_14,type,
    v44: state_type > $o ).

tff(pred_def_15,type,
    v54: state_type > $o ).

tff(pred_def_16,type,
    v53: state_type > $o ).

tff(pred_def_17,type,
    v34: state_type > $o ).

tff(pred_def_18,type,
    v32: state_type > $o ).

tff(pred_def_19,type,
    v66: state_type > $o ).

tff(pred_def_20,type,
    v84: state_type > $o ).

tff(pred_def_21,type,
    v82: state_type > $o ).

tff(pred_def_22,type,
    v94: state_type > $o ).

tff(pred_def_23,type,
    v112: ( state_type * $int ) > $o ).

tff(pred_def_24,type,
    v110: state_type > $o ).

tff(pred_def_25,type,
    v108: state_type > $o ).

tff(pred_def_26,type,
    v106: state_type > $o ).

tff(pred_def_27,type,
    v104: state_type > $o ).

tff(pred_def_28,type,
    v102: state_type > $o ).

tff(pred_def_29,type,
    v100: state_type > $o ).

tff(pred_def_30,type,
    v98: state_type > $o ).

tff(pred_def_31,type,
    v96: state_type > $o ).

tff(pred_def_32,type,
    v127: state_type > $o ).

tff(pred_def_33,type,
    b11: $int > $o ).

tff(pred_def_34,type,
    v148: ( state_type * $int ) > $o ).

tff(pred_def_35,type,
    v146: state_type > $o ).

tff(pred_def_36,type,
    v144: state_type > $o ).

tff(pred_def_37,type,
    v142: state_type > $o ).

tff(pred_def_38,type,
    v140: state_type > $o ).

tff(pred_def_39,type,
    v138: state_type > $o ).

tff(pred_def_40,type,
    v136: state_type > $o ).

tff(pred_def_41,type,
    v134: state_type > $o ).

tff(pred_def_42,type,
    v132: state_type > $o ).

tff(pred_def_43,type,
    v197: ( state_type * $int ) > $o ).

tff(pred_def_44,type,
    v199: ( state_type * $int ) > $o ).

tff(pred_def_45,type,
    v195: ( state_type * $int ) > $o ).

tff(pred_def_46,type,
    v193: state_type > $o ).

tff(pred_def_47,type,
    v205: ( state_type * $int ) > $o ).

tff(pred_def_48,type,
    v207: ( state_type * $int ) > $o ).

tff(pred_def_49,type,
    v203: ( state_type * $int ) > $o ).

tff(pred_def_50,type,
    v201: state_type > $o ).

tff(pred_def_51,type,
    v191: state_type > $o ).

tff(pred_def_52,type,
    v189: state_type > $o ).

tff(pred_def_53,type,
    v187: state_type > $o ).

tff(pred_def_54,type,
    v185: state_type > $o ).

tff(pred_def_55,type,
    v183: state_type > $o ).

tff(pred_def_56,type,
    v181: state_type > $o ).

tff(pred_def_57,type,
    v179: state_type > $o ).

tff(pred_def_58,type,
    v177: state_type > $o ).

tff(pred_def_59,type,
    v175: state_type > $o ).

tff(pred_def_60,type,
    v173: state_type > $o ).

tff(pred_def_61,type,
    v223: ( state_type * $int ) > $o ).

tff(pred_def_62,type,
    v218: ( state_type * $int ) > $o ).

tff(pred_def_64,type,
    v216: ( state_type * $int ) > $o ).

tff(pred_def_65,type,
    v214: ( state_type * $int ) > $o ).

tff(pred_def_66,type,
    b0000: $int > $o ).

tff(pred_def_67,type,
    v229: ( state_type * $int ) > $o ).

tff(pred_def_68,type,
    v227: state_type > $o ).

tff(pred_def_69,type,
    v225: state_type > $o ).

tff(pred_def_70,type,
    v212: ( state_type * $int ) > $o ).

tff(pred_def_71,type,
    v233: state_type > $o ).

tff(pred_def_72,type,
    v234: state_type > $o ).

tff(pred_def_73,type,
    v210: state_type > $o ).

tff(pred_def_74,type,
    v244: ( state_type * $int ) > $o ).

tff(pred_def_75,type,
    v242: ( state_type * $int ) > $o ).

tff(pred_def_76,type,
    v240: ( state_type * $int ) > $o ).

tff(pred_def_77,type,
    v238: ( state_type * $int ) > $o ).

tff(pred_def_78,type,
    v246: state_type > $o ).

tff(pred_def_79,type,
    v248: state_type > $o ).

tff(pred_def_80,type,
    v250: state_type > $o ).

tff(pred_def_81,type,
    v251: state_type > $o ).

tff(pred_def_82,type,
    v236: state_type > $o ).

tff(pred_def_83,type,
    v257: ( state_type * $int ) > $o ).

tff(pred_def_84,type,
    b010: $int > $o ).

tff(pred_def_85,type,
    v256: state_type > $o ).

tff(pred_def_86,type,
    v261: ( state_type * $int ) > $o ).

tff(pred_def_87,type,
    b001: $int > $o ).

tff(pred_def_88,type,
    v260: state_type > $o ).

tff(pred_def_89,type,
    v259: state_type > $o ).

tff(pred_def_90,type,
    v258: state_type > $o ).

tff(pred_def_91,type,
    v255: state_type > $o ).

tff(pred_def_92,type,
    v262: state_type > $o ).

tff(pred_def_93,type,
    v171: state_type > $o ).

tff(pred_def_94,type,
    v169: state_type > $o ).

tff(pred_def_95,type,
    v167: state_type > $o ).

tff(pred_def_96,type,
    v165: state_type > $o ).

tff(pred_def_97,type,
    b01: $int > $o ).

tff(pred_def_98,type,
    v88: ( state_type * $int ) > $o ).

tff(pred_def_99,type,
    v271: state_type > $o ).

tff(pred_def_100,type,
    v90: state_type > $o ).

tff(pred_def_101,type,
    v272: state_type > $o ).

tff(pred_def_102,type,
    v270: state_type > $o ).

tff(pred_def_103,type,
    v273: state_type > $o ).

tff(pred_def_104,type,
    v269: state_type > $o ).

tff(pred_def_105,type,
    v121: state_type > $o ).

tff(pred_def_106,type,
    v276: state_type > $o ).

tff(pred_def_107,type,
    v158: state_type > $o ).

tff(pred_def_108,type,
    v275: state_type > $o ).

tff(pred_def_109,type,
    v274: state_type > $o ).

tff(pred_def_110,type,
    v268: state_type > $o ).

tff(pred_def_111,type,
    v278: state_type > $o ).

tff(pred_def_112,type,
    v277: state_type > $o ).

tff(pred_def_113,type,
    v266: state_type > $o ).

tff(pred_def_114,type,
    v156: state_type > $o ).

tff(pred_def_115,type,
    v264: state_type > $o ).

tff(pred_def_116,type,
    v283: ( state_type * $int ) > $o ).

tff(pred_def_117,type,
    v282: state_type > $o ).

tff(pred_def_118,type,
    v160: ( state_type * $int ) > $o ).

tff(pred_def_119,type,
    v293: state_type > $o ).

tff(pred_def_120,type,
    v292: state_type > $o ).

tff(pred_def_121,type,
    v291: state_type > $o ).

tff(pred_def_122,type,
    v294: state_type > $o ).

tff(pred_def_123,type,
    v290: state_type > $o ).

tff(pred_def_124,type,
    v289: state_type > $o ).

tff(pred_def_125,type,
    v288: state_type > $o ).

tff(pred_def_126,type,
    v287: state_type > $o ).

tff(pred_def_127,type,
    v296: state_type > $o ).

tff(pred_def_128,type,
    v295: state_type > $o ).

tff(pred_def_129,type,
    v286: state_type > $o ).

tff(pred_def_130,type,
    v299: state_type > $o ).

tff(pred_def_131,type,
    v298: state_type > $o ).

tff(pred_def_132,type,
    v300: state_type > $o ).

tff(pred_def_133,type,
    v297: state_type > $o ).

tff(pred_def_134,type,
    v303: state_type > $o ).

tff(pred_def_135,type,
    v302: state_type > $o ).

tff(pred_def_136,type,
    v304: state_type > $o ).

tff(pred_def_137,type,
    v301: state_type > $o ).

tff(pred_def_138,type,
    v284: ( state_type * $int ) > $o ).

tff(pred_def_139,type,
    v306: ( state_type * $int ) > $o ).

tff(pred_def_140,type,
    b10: $int > $o ).

tff(pred_def_141,type,
    v305: state_type > $o ).

tff(pred_def_142,type,
    v313: state_type > $o ).

tff(pred_def_143,type,
    v312: state_type > $o ).

tff(pred_def_144,type,
    v311: state_type > $o ).

tff(pred_def_145,type,
    v310: state_type > $o ).

tff(pred_def_146,type,
    v314: state_type > $o ).

tff(pred_def_147,type,
    v309: state_type > $o ).

tff(pred_def_148,type,
    v317: state_type > $o ).

tff(pred_def_149,type,
    v316: state_type > $o ).

tff(pred_def_150,type,
    v318: state_type > $o ).

tff(pred_def_151,type,
    v315: state_type > $o ).

tff(pred_def_152,type,
    v320: state_type > $o ).

tff(pred_def_153,type,
    v321: state_type > $o ).

tff(pred_def_154,type,
    v319: state_type > $o ).

tff(pred_def_155,type,
    v307: ( state_type * $int ) > $o ).

tff(pred_def_156,type,
    v324: ( state_type * $int ) > $o ).

tff(pred_def_157,type,
    b00: $int > $o ).

tff(pred_def_158,type,
    v323: state_type > $o ).

tff(pred_def_159,type,
    v326: ( state_type * $int ) > $o ).

tff(pred_def_160,type,
    v325: state_type > $o ).

tff(pred_def_161,type,
    v322: state_type > $o ).

tff(pred_def_162,type,
    v163: ( state_type * $int ) > $o ).

tff(pred_def_163,type,
    v332: state_type > $o ).

tff(pred_def_164,type,
    v1: state_type > $o ).

tff(pred_def_165,type,
    v330: state_type > $o ).

tff(pred_def_166,type,
    v328: state_type > $o ).

tff(pred_def_167,type,
    v339: state_type > $o ).

tff(pred_def_168,type,
    nextState: ( state_type * state_type ) > $o ).

tff(pred_def_169,type,
    v337: state_type > $o ).

tff(pred_def_170,type,
    v336: state_type > $o ).

tff(pred_def_171,type,
    v335: state_type > $o ).

tff(pred_def_172,type,
    v346: state_type > $o ).

tff(pred_def_173,type,
    b1000: $int > $o ).

tff(pred_def_174,type,
    v343: ( state_type * $int ) > $o ).

tff(pred_def_175,type,
    v345: ( state_type * $int ) > $o ).

tff(pred_def_176,type,
    undeclared: $o ).

tff(pred_def_177,type,
    v351: state_type > $o ).

tff(pred_def_178,type,
    v355: state_type > $o ).

tff(pred_def_179,type,
    v356: state_type > $o ).

tff(pred_def_180,type,
    v354: state_type > $o ).

tff(pred_def_181,type,
    v353: state_type > $o ).

tff(pred_def_182,type,
    v357: state_type > $o ).

tff(pred_def_183,type,
    v154: state_type > $o ).

tff(pred_def_184,type,
    v152: state_type > $o ).

tff(pred_def_185,type,
    v362: ( state_type * $int ) > $o ).

tff(pred_def_186,type,
    v361: state_type > $o ).

tff(pred_def_187,type,
    v364: ( state_type * $int ) > $o ).

tff(pred_def_188,type,
    v363: state_type > $o ).

tff(pred_def_189,type,
    b000: $int > $o ).

tff(pred_def_190,type,
    v125: ( state_type * $int ) > $o ).

tff(pred_def_191,type,
    v366: state_type > $o ).

tff(pred_def_192,type,
    v374: ( state_type * $int ) > $o ).

tff(pred_def_193,type,
    v379: state_type > $o ).

tff(pred_def_194,type,
    v378: state_type > $o ).

tff(pred_def_195,type,
    v377: state_type > $o ).

tff(pred_def_196,type,
    v380: state_type > $o ).

tff(pred_def_197,type,
    v376: state_type > $o ).

tff(pred_def_198,type,
    v373: state_type > $o ).

tff(pred_def_199,type,
    v372: state_type > $o ).

tff(pred_def_200,type,
    v371: state_type > $o ).

tff(pred_def_201,type,
    v382: state_type > $o ).

tff(pred_def_202,type,
    v381: state_type > $o ).

tff(pred_def_203,type,
    v370: state_type > $o ).

tff(pred_def_204,type,
    v385: state_type > $o ).

tff(pred_def_205,type,
    v384: state_type > $o ).

tff(pred_def_206,type,
    v386: state_type > $o ).

tff(pred_def_207,type,
    v383: state_type > $o ).

tff(pred_def_208,type,
    v389: state_type > $o ).

tff(pred_def_209,type,
    v388: state_type > $o ).

tff(pred_def_210,type,
    v390: state_type > $o ).

tff(pred_def_211,type,
    v387: state_type > $o ).

tff(pred_def_212,type,
    v368: ( state_type * $int ) > $o ).

tff(pred_def_213,type,
    v367: ( state_type * $int ) > $o ).

tff(pred_def_214,type,
    b00000000000000000000000000000000: $int > $o ).

tff(pred_def_215,type,
    v365: ( state_type * $int ) > $o ).

tff(pred_def_216,type,
    v393: ( state_type * $int ) > $o ).

tff(pred_def_217,type,
    v392: state_type > $o ).

tff(pred_def_218,type,
    b100: $int > $o ).

tff(pred_def_219,type,
    v395: state_type > $o ).

tff(pred_def_220,type,
    v401: state_type > $o ).

tff(pred_def_221,type,
    v400: state_type > $o ).

tff(pred_def_222,type,
    v402: state_type > $o ).

tff(pred_def_223,type,
    v399: state_type > $o ).

tff(pred_def_224,type,
    v403: state_type > $o ).

tff(pred_def_225,type,
    v398: state_type > $o ).

tff(pred_def_226,type,
    v406: state_type > $o ).

tff(pred_def_227,type,
    v407: state_type > $o ).

tff(pred_def_228,type,
    v405: state_type > $o ).

tff(pred_def_229,type,
    v408: state_type > $o ).

tff(pred_def_230,type,
    v404: state_type > $o ).

tff(pred_def_231,type,
    v396: ( state_type * $int ) > $o ).

tff(pred_def_232,type,
    v394: ( state_type * $int ) > $o ).

tff(pred_def_233,type,
    v410: ( state_type * $int ) > $o ).

tff(pred_def_234,type,
    v409: state_type > $o ).

tff(pred_def_235,type,
    v130: ( state_type * $int ) > $o ).

tff(pred_def_236,type,
    v412: state_type > $o ).

tff(pred_def_237,type,
    v419: state_type > $o ).

tff(pred_def_238,type,
    v417: state_type > $o ).

tff(pred_def_239,type,
    v416: state_type > $o ).

tff(pred_def_240,type,
    v415: state_type > $o ).

tff(pred_def_241,type,
    v426: state_type > $o ).

tff(pred_def_242,type,
    v423: ( state_type * $int ) > $o ).

tff(pred_def_243,type,
    v425: ( state_type * $int ) > $o ).

tff(pred_def_244,type,
    v123: state_type > $o ).

tff(pred_def_245,type,
    v433: ( state_type * $int ) > $o ).

tff(pred_def_246,type,
    v436: state_type > $o ).

tff(pred_def_247,type,
    v431: state_type > $o ).

tff(pred_def_248,type,
    v443: state_type > $o ).

tff(pred_def_249,type,
    v442: state_type > $o ).

tff(pred_def_250,type,
    v444: state_type > $o ).

tff(pred_def_251,type,
    v441: state_type > $o ).

tff(pred_def_252,type,
    v440: state_type > $o ).

tff(pred_def_253,type,
    v445: state_type > $o ).

tff(pred_def_254,type,
    v439: state_type > $o ).

tff(pred_def_255,type,
    v446: state_type > $o ).

tff(pred_def_256,type,
    v438: state_type > $o ).

tff(pred_def_257,type,
    v449: state_type > $o ).

tff(pred_def_258,type,
    v450: state_type > $o ).

tff(pred_def_259,type,
    v448: state_type > $o ).

tff(pred_def_260,type,
    v447: state_type > $o ).

tff(pred_def_261,type,
    v116: state_type > $o ).

tff(pred_def_262,type,
    v114: state_type > $o ).

tff(pred_def_263,type,
    v456: ( state_type * $int ) > $o ).

tff(pred_def_264,type,
    v455: ( state_type * $int ) > $o ).

tff(pred_def_265,type,
    v454: ( state_type * $int ) > $o ).

tff(pred_def_266,type,
    v459: state_type > $o ).

tff(pred_def_267,type,
    v466: state_type > $o ).

tff(pred_def_268,type,
    v464: state_type > $o ).

tff(pred_def_269,type,
    v463: state_type > $o ).

tff(pred_def_270,type,
    v476: state_type > $o ).

tff(pred_def_271,type,
    v452: ( state_type * $int ) > $o ).

tff(pred_def_272,type,
    v477: state_type > $o ).

tff(pred_def_273,type,
    v475: state_type > $o ).

tff(pred_def_274,type,
    v478: state_type > $o ).

tff(pred_def_275,type,
    v474: state_type > $o ).

tff(pred_def_276,type,
    v473: state_type > $o ).

tff(pred_def_277,type,
    v479: state_type > $o ).

tff(pred_def_278,type,
    v470: state_type > $o ).

tff(pred_def_279,type,
    v472: state_type > $o ).

tff(pred_def_280,type,
    v462: state_type > $o ).

tff(pred_def_281,type,
    v483: state_type > $o ).

tff(pred_def_282,type,
    v480: state_type > $o ).

tff(pred_def_283,type,
    v482: state_type > $o ).

tff(pred_def_284,type,
    v92: state_type > $o ).

tff(pred_def_285,type,
    v503: state_type > $o ).

tff(pred_def_286,type,
    v504: ( state_type * $int ) > $o ).

tff(pred_def_287,type,
    v507: ( state_type * $int ) > $o ).

tff(pred_def_288,type,
    v506: state_type > $o ).

tff(pred_def_289,type,
    v509: ( state_type * $int ) > $o ).

tff(pred_def_290,type,
    v508: state_type > $o ).

tff(pred_def_291,type,
    v510: ( state_type * $int ) > $o ).

tff(pred_def_292,type,
    v513: ( state_type * $int ) > $o ).

tff(pred_def_293,type,
    v512: state_type > $o ).

tff(pred_def_294,type,
    v514: ( state_type * $int ) > $o ).

tff(pred_def_295,type,
    v517: ( state_type * $int ) > $o ).

tff(pred_def_296,type,
    v516: state_type > $o ).

tff(pred_def_297,type,
    v505: ( state_type * $int ) > $o ).

tff(pred_def_298,type,
    v502: ( state_type * $int ) > $o ).

tff(pred_def_299,type,
    v500: ( state_type * $int ) > $o ).

tff(pred_def_300,type,
    v498: state_type > $o ).

tff(pred_def_301,type,
    v533: ( state_type * $int ) > $o ).

tff(pred_def_302,type,
    v531: ( state_type * $int ) > $o ).

tff(pred_def_303,type,
    v529: ( state_type * $int ) > $o ).

tff(pred_def_304,type,
    v527: ( state_type * $int ) > $o ).

tff(pred_def_305,type,
    v525: ( state_type * $int ) > $o ).

tff(pred_def_306,type,
    v523: ( state_type * $int ) > $o ).

tff(pred_def_307,type,
    v521: ( state_type * $int ) > $o ).

tff(pred_def_308,type,
    v519: ( state_type * $int ) > $o ).

tff(pred_def_309,type,
    v493: ( state_type * $int ) > $o ).

tff(pred_def_310,type,
    v535: ( state_type * $int ) > $o ).

tff(pred_def_311,type,
    v536: ( state_type * $int ) > $o ).

tff(pred_def_312,type,
    v496: ( state_type * $int ) > $o ).

tff(pred_def_313,type,
    v540: state_type > $o ).

tff(pred_def_314,type,
    v542: ( state_type * $int ) > $o ).

tff(pred_def_315,type,
    v543: ( state_type * $int ) > $o ).

tff(pred_def_316,type,
    v538: ( state_type * $int ) > $o ).

tff(pred_def_317,type,
    v548: state_type > $o ).

tff(pred_def_318,type,
    v547: state_type > $o ).

tff(pred_def_319,type,
    v556: state_type > $o ).

tff(pred_def_320,type,
    v561: ( state_type * $int ) > $o ).

tff(pred_def_321,type,
    v560: state_type > $o ).

tff(pred_def_322,type,
    v563: ( state_type * $int ) > $o ).

tff(pred_def_323,type,
    v562: state_type > $o ).

tff(pred_def_324,type,
    v559: state_type > $o ).

tff(pred_def_325,type,
    v565: ( state_type * $int ) > $o ).

tff(pred_def_326,type,
    v564: state_type > $o ).

tff(pred_def_327,type,
    v558: state_type > $o ).

tff(pred_def_328,type,
    v566: state_type > $o ).

tff(pred_def_329,type,
    v557: state_type > $o ).

tff(pred_def_330,type,
    v555: state_type > $o ).

tff(pred_def_331,type,
    v570: ( state_type * $int ) > $o ).

tff(pred_def_332,type,
    v569: state_type > $o ).

tff(pred_def_333,type,
    v568: state_type > $o ).

tff(pred_def_334,type,
    v567: state_type > $o ).

tff(pred_def_335,type,
    v552: state_type > $o ).

tff(pred_def_336,type,
    v554: state_type > $o ).

tff(pred_def_337,type,
    v546: state_type > $o ).

tff(pred_def_338,type,
    v574: ( state_type * $int ) > $o ).

tff(pred_def_339,type,
    b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000: $int > $o ).

tff(pred_def_340,type,
    v571: ( state_type * $int ) > $o ).

tff(pred_def_341,type,
    v573: ( state_type * $int ) > $o ).

tff(pred_def_342,type,
    v545: ( state_type * $int ) > $o ).

tff(pred_def_343,type,
    v491: ( state_type * $int ) > $o ).

tff(pred_def_344,type,
    v489: ( state_type * $int ) > $o ).

tff(pred_def_345,type,
    v487: ( state_type * $int ) > $o ).

tff(pred_def_346,type,
    v591: state_type > $o ).

tff(pred_def_347,type,
    v589: state_type > $o ).

tff(pred_def_348,type,
    v588: state_type > $o ).

tff(pred_def_349,type,
    v586: ( state_type * $int ) > $o ).

tff(pred_def_350,type,
    v584: state_type > $o ).

tff(pred_def_351,type,
    v613: state_type > $o ).

tff(pred_def_352,type,
    v614: state_type > $o ).

tff(pred_def_353,type,
    v612: state_type > $o ).

tff(pred_def_354,type,
    v615: state_type > $o ).

tff(pred_def_355,type,
    v611: state_type > $o ).

tff(pred_def_356,type,
    v616: state_type > $o ).

tff(pred_def_357,type,
    v610: state_type > $o ).

tff(pred_def_358,type,
    v617: state_type > $o ).

tff(pred_def_359,type,
    v609: state_type > $o ).

tff(pred_def_360,type,
    v618: state_type > $o ).

tff(pred_def_361,type,
    v608: state_type > $o ).

tff(pred_def_362,type,
    v619: state_type > $o ).

tff(pred_def_363,type,
    v606: state_type > $o ).

tff(pred_def_364,type,
    v622: state_type > $o ).

tff(pred_def_365,type,
    v620: state_type > $o ).

tff(pred_def_366,type,
    v605: state_type > $o ).

tff(pred_def_367,type,
    v629: state_type > $o ).

tff(pred_def_368,type,
    v628: state_type > $o ).

tff(pred_def_369,type,
    v627: state_type > $o ).

tff(pred_def_370,type,
    v626: state_type > $o ).

tff(pred_def_371,type,
    v625: state_type > $o ).

tff(pred_def_372,type,
    v623: state_type > $o ).

tff(pred_def_373,type,
    v604: state_type > $o ).

tff(pred_def_374,type,
    v632: state_type > $o ).

tff(pred_def_375,type,
    v630: state_type > $o ).

tff(pred_def_376,type,
    v603: state_type > $o ).

tff(pred_def_377,type,
    v633: state_type > $o ).

tff(pred_def_378,type,
    v602: state_type > $o ).

tff(pred_def_379,type,
    v635: state_type > $o ).

tff(pred_def_380,type,
    v600: state_type > $o ).

tff(pred_def_381,type,
    v643: state_type > $o ).

tff(pred_def_382,type,
    v642: state_type > $o ).

tff(pred_def_383,type,
    v641: state_type > $o ).

tff(pred_def_384,type,
    v640: state_type > $o ).

tff(pred_def_385,type,
    v639: state_type > $o ).

tff(pred_def_386,type,
    v637: state_type > $o ).

tff(pred_def_387,type,
    v644: ( state_type * $int ) > $o ).

tff(pred_def_388,type,
    v646: state_type > $o ).

tff(pred_def_389,type,
    v652: state_type > $o ).

tff(pred_def_390,type,
    v651: state_type > $o ).

tff(pred_def_391,type,
    v650: state_type > $o ).

tff(pred_def_392,type,
    v648: state_type > $o ).

tff(pred_def_393,type,
    v645: state_type > $o ).

tff(pred_def_394,type,
    v660: state_type > $o ).

tff(pred_def_395,type,
    v659: state_type > $o ).

tff(pred_def_396,type,
    v658: state_type > $o ).

tff(pred_def_397,type,
    v656: state_type > $o ).

tff(pred_def_398,type,
    v663: state_type > $o ).

tff(pred_def_399,type,
    v661: state_type > $o ).

tff(pred_def_400,type,
    v655: state_type > $o ).

tff(pred_def_401,type,
    v667: state_type > $o ).

tff(pred_def_402,type,
    v666: state_type > $o ).

tff(pred_def_403,type,
    v664: state_type > $o ).

tff(pred_def_404,type,
    v653: state_type > $o ).

tff(pred_def_405,type,
    v599: ( state_type * $int ) > $o ).

tff(pred_def_406,type,
    v671: state_type > $o ).

tff(pred_def_407,type,
    v672: state_type > $o ).

tff(pred_def_408,type,
    v670: state_type > $o ).

tff(pred_def_409,type,
    v673: state_type > $o ).

tff(pred_def_410,type,
    v669: state_type > $o ).

tff(pred_def_411,type,
    v674: state_type > $o ).

tff(pred_def_412,type,
    v86: state_type > $o ).

tff(pred_def_413,type,
    v679: state_type > $o ).

tff(pred_def_414,type,
    v678: state_type > $o ).

tff(pred_def_415,type,
    v677: state_type > $o ).

tff(pred_def_416,type,
    v686: state_type > $o ).

tff(pred_def_417,type,
    v683: state_type > $o ).

tff(pred_def_418,type,
    v685: state_type > $o ).

tff(pred_def_419,type,
    v80: state_type > $o ).

tff(pred_def_420,type,
    v78: state_type > $o ).

tff(pred_def_421,type,
    v76: state_type > $o ).

tff(pred_def_422,type,
    v74: state_type > $o ).

tff(pred_def_423,type,
    v72: state_type > $o ).

tff(pred_def_424,type,
    v70: state_type > $o ).

tff(pred_def_425,type,
    v6: ( state_type * $int ) > $o ).

tff(pred_def_426,type,
    v695: state_type > $o ).

tff(pred_def_427,type,
    v696: state_type > $o ).

tff(pred_def_428,type,
    v694: state_type > $o ).

tff(pred_def_429,type,
    v21: state_type > $o ).

tff(pred_def_430,type,
    v699: state_type > $o ).

tff(pred_def_431,type,
    v60: state_type > $o ).

tff(pred_def_432,type,
    v701: state_type > $o ).

tff(pred_def_433,type,
    v700: state_type > $o ).

tff(pred_def_434,type,
    v698: state_type > $o ).

tff(pred_def_435,type,
    v703: state_type > $o ).

tff(pred_def_436,type,
    v705: state_type > $o ).

tff(pred_def_437,type,
    v704: state_type > $o ).

tff(pred_def_438,type,
    v702: state_type > $o ).

tff(pred_def_439,type,
    v697: state_type > $o ).

tff(pred_def_440,type,
    v692: state_type > $o ).

tff(pred_def_441,type,
    v690: state_type > $o ).

tff(pred_def_442,type,
    v711: ( state_type * $int ) > $o ).

tff(pred_def_443,type,
    v710: state_type > $o ).

tff(pred_def_444,type,
    b00000: $int > $o ).

tff(pred_def_445,type,
    v64: ( state_type * $int ) > $o ).

tff(pred_def_446,type,
    v713: ( state_type * $int ) > $o ).

tff(pred_def_447,type,
    v712: state_type > $o ).

tff(pred_def_448,type,
    v715: state_type > $o ).

tff(pred_def_449,type,
    v723: ( state_type * $int ) > $o ).

tff(pred_def_450,type,
    v732: state_type > $o ).

tff(pred_def_451,type,
    v731: state_type > $o ).

tff(pred_def_452,type,
    v730: state_type > $o ).

tff(pred_def_453,type,
    v733: state_type > $o ).

tff(pred_def_454,type,
    v729: state_type > $o ).

tff(pred_def_455,type,
    v728: state_type > $o ).

tff(pred_def_456,type,
    v734: state_type > $o ).

tff(pred_def_457,type,
    v727: state_type > $o ).

tff(pred_def_458,type,
    v726: state_type > $o ).

tff(pred_def_459,type,
    v735: state_type > $o ).

tff(pred_def_460,type,
    v725: state_type > $o ).

tff(pred_def_461,type,
    v722: state_type > $o ).

tff(pred_def_462,type,
    v721: state_type > $o ).

tff(pred_def_463,type,
    v720: state_type > $o ).

tff(pred_def_464,type,
    v737: state_type > $o ).

tff(pred_def_465,type,
    v736: state_type > $o ).

tff(pred_def_466,type,
    v719: state_type > $o ).

tff(pred_def_467,type,
    v740: state_type > $o ).

tff(pred_def_468,type,
    v739: state_type > $o ).

tff(pred_def_469,type,
    v741: state_type > $o ).

tff(pred_def_470,type,
    v738: state_type > $o ).

tff(pred_def_471,type,
    v744: state_type > $o ).

tff(pred_def_472,type,
    v743: state_type > $o ).

tff(pred_def_473,type,
    v745: state_type > $o ).

tff(pred_def_474,type,
    v742: state_type > $o ).

tff(pred_def_475,type,
    v748: state_type > $o ).

tff(pred_def_476,type,
    v747: state_type > $o ).

tff(pred_def_477,type,
    v749: state_type > $o ).

tff(pred_def_478,type,
    v746: state_type > $o ).

tff(pred_def_479,type,
    v752: state_type > $o ).

tff(pred_def_480,type,
    v751: state_type > $o ).

tff(pred_def_481,type,
    v753: state_type > $o ).

tff(pred_def_482,type,
    v750: state_type > $o ).

tff(pred_def_483,type,
    v717: ( state_type * $int ) > $o ).

tff(pred_def_484,type,
    v716: ( state_type * $int ) > $o ).

tff(pred_def_485,type,
    v714: ( state_type * $int ) > $o ).

tff(pred_def_486,type,
    v755: ( state_type * $int ) > $o ).

tff(pred_def_487,type,
    v754: state_type > $o ).

tff(pred_def_488,type,
    b01111: $int > $o ).

tff(pred_def_489,type,
    v757: state_type > $o ).

tff(pred_def_490,type,
    v765: state_type > $o ).

tff(pred_def_491,type,
    v764: state_type > $o ).

tff(pred_def_492,type,
    v763: state_type > $o ).

tff(pred_def_493,type,
    v762: state_type > $o ).

tff(pred_def_494,type,
    v766: state_type > $o ).

tff(pred_def_495,type,
    v761: state_type > $o ).

tff(pred_def_496,type,
    v767: state_type > $o ).

tff(pred_def_497,type,
    v760: state_type > $o ).

tff(pred_def_498,type,
    v770: state_type > $o ).

tff(pred_def_499,type,
    v771: state_type > $o ).

tff(pred_def_500,type,
    v769: state_type > $o ).

tff(pred_def_501,type,
    v772: state_type > $o ).

tff(pred_def_502,type,
    v768: state_type > $o ).

tff(pred_def_503,type,
    v775: state_type > $o ).

tff(pred_def_504,type,
    v776: state_type > $o ).

tff(pred_def_505,type,
    v774: state_type > $o ).

tff(pred_def_506,type,
    v777: state_type > $o ).

tff(pred_def_507,type,
    v773: state_type > $o ).

tff(pred_def_508,type,
    v780: state_type > $o ).

tff(pred_def_509,type,
    v781: state_type > $o ).

tff(pred_def_510,type,
    v779: state_type > $o ).

tff(pred_def_511,type,
    v782: state_type > $o ).

tff(pred_def_512,type,
    v778: state_type > $o ).

tff(pred_def_513,type,
    v758: ( state_type * $int ) > $o ).

tff(pred_def_514,type,
    v756: ( state_type * $int ) > $o ).

tff(pred_def_515,type,
    v784: ( state_type * $int ) > $o ).

tff(pred_def_516,type,
    v783: state_type > $o ).

tff(pred_def_517,type,
    v68: ( state_type * $int ) > $o ).

tff(pred_def_518,type,
    v790: state_type > $o ).

tff(pred_def_519,type,
    v788: state_type > $o ).

tff(pred_def_520,type,
    v786: state_type > $o ).

tff(pred_def_521,type,
    v797: state_type > $o ).

tff(pred_def_522,type,
    v795: state_type > $o ).

tff(pred_def_523,type,
    v794: state_type > $o ).

tff(pred_def_524,type,
    v793: state_type > $o ).

tff(pred_def_525,type,
    v804: state_type > $o ).

tff(pred_def_526,type,
    v801: ( state_type * $int ) > $o ).

tff(pred_def_527,type,
    v803: ( state_type * $int ) > $o ).

tff(pred_def_528,type,
    v62: state_type > $o ).

tff(pred_def_529,type,
    v809: state_type > $o ).

tff(pred_def_530,type,
    v812: state_type > $o ).

tff(pred_def_531,type,
    v811: state_type > $o ).

tff(pred_def_532,type,
    v814: state_type > $o ).

tff(pred_def_533,type,
    v813: state_type > $o ).

tff(pred_def_534,type,
    v810: state_type > $o ).

tff(pred_def_535,type,
    v58: state_type > $o ).

tff(pred_def_536,type,
    v56: state_type > $o ).

tff(pred_def_537,type,
    v817: ( state_type * $int ) > $o ).

tff(pred_def_538,type,
    v816: state_type > $o ).

tff(pred_def_539,type,
    v25: ( state_type * $int ) > $o ).

tff(pred_def_540,type,
    v819: ( state_type * $int ) > $o ).

tff(pred_def_541,type,
    v818: state_type > $o ).

tff(pred_def_542,type,
    v821: state_type > $o ).

tff(pred_def_543,type,
    v829: ( state_type * $int ) > $o ).

tff(pred_def_544,type,
    v837: state_type > $o ).

tff(pred_def_545,type,
    v836: state_type > $o ).

tff(pred_def_546,type,
    v835: state_type > $o ).

tff(pred_def_547,type,
    v838: state_type > $o ).

tff(pred_def_548,type,
    v834: state_type > $o ).

tff(pred_def_549,type,
    v833: state_type > $o ).

tff(pred_def_550,type,
    v839: state_type > $o ).

tff(pred_def_551,type,
    v832: state_type > $o ).

tff(pred_def_552,type,
    v831: state_type > $o ).

tff(pred_def_553,type,
    v840: state_type > $o ).

tff(pred_def_554,type,
    v830: state_type > $o ).

tff(pred_def_555,type,
    v828: state_type > $o ).

tff(pred_def_556,type,
    v827: state_type > $o ).

tff(pred_def_557,type,
    v826: state_type > $o ).

tff(pred_def_558,type,
    v842: state_type > $o ).

tff(pred_def_559,type,
    v841: state_type > $o ).

tff(pred_def_560,type,
    v825: state_type > $o ).

tff(pred_def_561,type,
    v845: state_type > $o ).

tff(pred_def_562,type,
    v844: state_type > $o ).

tff(pred_def_563,type,
    v846: state_type > $o ).

tff(pred_def_564,type,
    v843: state_type > $o ).

tff(pred_def_565,type,
    v849: state_type > $o ).

tff(pred_def_566,type,
    v848: state_type > $o ).

tff(pred_def_567,type,
    v850: state_type > $o ).

tff(pred_def_568,type,
    v847: state_type > $o ).

tff(pred_def_569,type,
    v853: state_type > $o ).

tff(pred_def_570,type,
    v852: state_type > $o ).

tff(pred_def_571,type,
    v854: state_type > $o ).

tff(pred_def_572,type,
    v851: state_type > $o ).

tff(pred_def_573,type,
    v857: state_type > $o ).

tff(pred_def_574,type,
    v856: state_type > $o ).

tff(pred_def_575,type,
    v858: state_type > $o ).

tff(pred_def_576,type,
    v855: state_type > $o ).

tff(pred_def_577,type,
    v823: ( state_type * $int ) > $o ).

tff(pred_def_578,type,
    v822: ( state_type * $int ) > $o ).

tff(pred_def_579,type,
    v820: ( state_type * $int ) > $o ).

tff(pred_def_580,type,
    v860: ( state_type * $int ) > $o ).

tff(pred_def_581,type,
    v859: state_type > $o ).

tff(pred_def_582,type,
    v862: state_type > $o ).

tff(pred_def_583,type,
    v870: state_type > $o ).

tff(pred_def_584,type,
    v869: state_type > $o ).

tff(pred_def_585,type,
    v868: state_type > $o ).

tff(pred_def_586,type,
    v867: state_type > $o ).

tff(pred_def_587,type,
    v871: state_type > $o ).

tff(pred_def_588,type,
    v866: state_type > $o ).

tff(pred_def_589,type,
    v872: state_type > $o ).

tff(pred_def_590,type,
    v865: state_type > $o ).

tff(pred_def_591,type,
    v875: state_type > $o ).

tff(pred_def_592,type,
    v876: state_type > $o ).

tff(pred_def_593,type,
    v874: state_type > $o ).

tff(pred_def_594,type,
    v877: state_type > $o ).

tff(pred_def_595,type,
    v873: state_type > $o ).

tff(pred_def_596,type,
    v880: state_type > $o ).

tff(pred_def_597,type,
    v881: state_type > $o ).

tff(pred_def_598,type,
    v879: state_type > $o ).

tff(pred_def_599,type,
    v882: state_type > $o ).

tff(pred_def_600,type,
    v878: state_type > $o ).

tff(pred_def_601,type,
    v885: state_type > $o ).

tff(pred_def_602,type,
    v886: state_type > $o ).

tff(pred_def_603,type,
    v884: state_type > $o ).

tff(pred_def_604,type,
    v887: state_type > $o ).

tff(pred_def_605,type,
    v883: state_type > $o ).

tff(pred_def_606,type,
    v863: ( state_type * $int ) > $o ).

tff(pred_def_607,type,
    v861: ( state_type * $int ) > $o ).

tff(pred_def_608,type,
    v889: ( state_type * $int ) > $o ).

tff(pred_def_609,type,
    v888: state_type > $o ).

tff(pred_def_610,type,
    v30: ( state_type * $int ) > $o ).

tff(pred_def_611,type,
    v891: state_type > $o ).

tff(pred_def_612,type,
    v898: state_type > $o ).

tff(pred_def_613,type,
    v896: state_type > $o ).

tff(pred_def_614,type,
    v895: state_type > $o ).

tff(pred_def_615,type,
    v894: state_type > $o ).

tff(pred_def_616,type,
    v905: state_type > $o ).

tff(pred_def_617,type,
    v902: ( state_type * $int ) > $o ).

tff(pred_def_618,type,
    v904: ( state_type * $int ) > $o ).

tff(pred_def_619,type,
    v23: state_type > $o ).

tff(pred_def_620,type,
    v912: state_type > $o ).

tff(pred_def_621,type,
    v911: state_type > $o ).

tff(pred_def_622,type,
    v913: state_type > $o ).

tff(pred_def_623,type,
    v910: state_type > $o ).

tff(pred_def_624,type,
    v915: state_type > $o ).

tff(pred_def_625,type,
    v914: state_type > $o ).

tff(pred_def_626,type,
    v19: ( state_type * $int ) > $o ).

tff(pred_def_627,type,
    v918: state_type > $o ).

tff(pred_def_628,type,
    v920: state_type > $o ).

tff(pred_def_629,type,
    v919: state_type > $o ).

tff(pred_def_630,type,
    v917: state_type > $o ).

tff(pred_def_631,type,
    v922: state_type > $o ).

tff(pred_def_632,type,
    v921: state_type > $o ).

tff(pred_def_633,type,
    v929: state_type > $o ).

tff(pred_def_634,type,
    v927: state_type > $o ).

tff(pred_def_635,type,
    v926: state_type > $o ).

tff(pred_def_636,type,
    v925: state_type > $o ).

tff(pred_def_637,type,
    v936: state_type > $o ).

tff(pred_def_638,type,
    v933: state_type > $o ).

tff(pred_def_639,type,
    v935: state_type > $o ).

tff(pred_def_640,type,
    v944: state_type > $o ).

tff(pred_def_641,type,
    v942: state_type > $o ).

tff(pred_def_642,type,
    v941: state_type > $o ).

tff(pred_def_643,type,
    v947: state_type > $o ).

tff(pred_def_644,type,
    v949: state_type > $o ).

tff(pred_def_645,type,
    v957: state_type > $o ).

tff(pred_def_646,type,
    v956: state_type > $o ).

tff(pred_def_647,type,
    v958: state_type > $o ).

tff(pred_def_648,type,
    v954: state_type > $o ).

tff(pred_def_649,type,
    v953: state_type > $o ).

tff(pred_def_650,type,
    v4: state_type > $o ).

tff(pred_def_651,type,
    reachableState: state_type > $o ).

tff(pathAxiom_19,axiom,
    nextState(constB19,constB20) ).

tff(pathAxiom_18,axiom,
    nextState(constB18,constB19) ).

tff(pathAxiom_17,axiom,
    nextState(constB17,constB18) ).

tff(pathAxiom_16,axiom,
    nextState(constB16,constB17) ).

tff(pathAxiom_15,axiom,
    nextState(constB15,constB16) ).

tff(pathAxiom_14,axiom,
    nextState(constB14,constB15) ).

tff(pathAxiom_13,axiom,
    nextState(constB13,constB14) ).

tff(pathAxiom_12,axiom,
    nextState(constB12,constB13) ).

tff(pathAxiom_11,axiom,
    nextState(constB11,constB12) ).

tff(pathAxiom_10,axiom,
    nextState(constB10,constB11) ).

tff(pathAxiom_9,axiom,
    nextState(constB9,constB10) ).

tff(pathAxiom_8,axiom,
    nextState(constB8,constB9) ).

tff(pathAxiom_7,axiom,
    nextState(constB7,constB8) ).

tff(pathAxiom_6,axiom,
    nextState(constB6,constB7) ).

tff(pathAxiom_5,axiom,
    nextState(constB5,constB6) ).

tff(pathAxiom_4,axiom,
    nextState(constB4,constB5) ).

tff(pathAxiom_3,axiom,
    nextState(constB3,constB4) ).

tff(pathAxiom_2,axiom,
    nextState(constB2,constB3) ).

tff(pathAxiom_1,axiom,
    nextState(constB1,constB2) ).

tff(pathAxiom,axiom,
    nextState(constB0,constB1) ).

tff(reachableStateAxiom_22,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( reachableState(VarCurr)
        & reachableState(VarNext) ) ) ).

tff(reachableStateAxiom_21,axiom,
    ! [VarState: state_type] :
      ( reachableState(VarState)
     => ( ( constB0 = VarState )
        | ( constB1 = VarState )
        | ( constB2 = VarState )
        | ( constB3 = VarState )
        | ( constB4 = VarState )
        | ( constB5 = VarState )
        | ( constB6 = VarState )
        | ( constB7 = VarState )
        | ( constB8 = VarState )
        | ( constB9 = VarState )
        | ( constB10 = VarState )
        | ( constB11 = VarState )
        | ( constB12 = VarState )
        | ( constB13 = VarState )
        | ( constB14 = VarState )
        | ( constB15 = VarState )
        | ( constB16 = VarState )
        | ( constB17 = VarState )
        | ( constB18 = VarState )
        | ( constB19 = VarState )
        | ( constB20 = VarState ) ) ) ).

tff(reachableStateAxiom_20,axiom,
    reachableState(constB20) ).

tff(reachableStateAxiom_19,axiom,
    reachableState(constB19) ).

tff(reachableStateAxiom_18,axiom,
    reachableState(constB18) ).

tff(reachableStateAxiom_17,axiom,
    reachableState(constB17) ).

tff(reachableStateAxiom_16,axiom,
    reachableState(constB16) ).

tff(reachableStateAxiom_15,axiom,
    reachableState(constB15) ).

tff(reachableStateAxiom_14,axiom,
    reachableState(constB14) ).

tff(reachableStateAxiom_13,axiom,
    reachableState(constB13) ).

tff(reachableStateAxiom_12,axiom,
    reachableState(constB12) ).

tff(reachableStateAxiom_11,axiom,
    reachableState(constB11) ).

tff(reachableStateAxiom_10,axiom,
    reachableState(constB10) ).

tff(reachableStateAxiom_9,axiom,
    reachableState(constB9) ).

tff(reachableStateAxiom_8,axiom,
    reachableState(constB8) ).

tff(reachableStateAxiom_7,axiom,
    reachableState(constB7) ).

tff(reachableStateAxiom_6,axiom,
    reachableState(constB6) ).

tff(reachableStateAxiom_5,axiom,
    reachableState(constB5) ).

tff(reachableStateAxiom_4,axiom,
    reachableState(constB4) ).

tff(reachableStateAxiom_3,axiom,
    reachableState(constB3) ).

tff(reachableStateAxiom_2,axiom,
    reachableState(constB2) ).

tff(reachableStateAxiom_1,axiom,
    reachableState(constB1) ).

tff(reachableStateAxiom,axiom,
    reachableState(constB0) ).

tff(clock_toggling,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v1(VarCurr)
      <=> ~ v1(VarNext) ) ) ).

tff(clock_pattern,axiom,
    ~ v1(constB0) ).

tff(addAssertion,conjecture,
    ! [VarCurr: state_type] :
      ( reachableState(VarCurr)
     => v4(VarCurr) ) ).

tff(writeUnaryOperator_104,axiom,
    ! [VarCurr: state_type] :
      ( ~ v4(VarCurr)
    <=> v953(VarCurr) ) ).

tff(writeUnaryOperator_103,axiom,
    ! [VarCurr: state_type] :
      ( ~ v953(VarCurr)
    <=> v954(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_161,axiom,
    ! [VarCurr: state_type] :
      ( v954(VarCurr)
    <=> ( v956(VarCurr)
        & v958(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_70,axiom,
    ! [VarCurr: state_type] :
      ( v958(VarCurr)
    <=> ( v6(VarCurr,0)
        | v6(VarCurr,1) ) ) ).

tff(writeUnaryOperator_102,axiom,
    ! [VarCurr: state_type] :
      ( ~ v956(VarCurr)
    <=> v957(VarCurr) ) ).

tff(writeBinaryOperatorShiftedRanges_69,axiom,
    ! [VarCurr: state_type] :
      ( v957(VarCurr)
    <=> ( v6(VarCurr,0)
        & v6(VarCurr,1) ) ) ).

tff(addCaseBooleanConditionEqualRanges1_7,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v941(VarNext)
       => ( v6(VarNext,1)
        <=> v6(VarCurr,1) ) ) ) ).

tff(addCaseBooleanConditionShiftedRanges0,axiom,
    ! [VarNext: state_type] :
      ( v941(VarNext)
     => ( v6(VarNext,1)
      <=> v949(VarNext) ) ) ).

tff(addAssignment_237,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v949(VarNext)
      <=> v947(VarCurr) ) ) ).

tff(addConditionBooleanCondShiftedRangesElseBranch_1,axiom,
    ! [VarCurr: state_type] :
      ( ~ v936(VarCurr)
     => ( v947(VarCurr)
      <=> v19(VarCurr,1) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_41,axiom,
    ! [VarCurr: state_type] :
      ( v936(VarCurr)
     => ( v947(VarCurr)
      <=> $false ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_160,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v941(VarNext)
      <=> v942(VarNext) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_159,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v942(VarNext)
      <=> ( v944(VarNext)
          & v788(VarNext) ) ) ) ).

tff(writeUnaryOperator_101,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v944(VarNext)
      <=> v929(VarNext) ) ) ).

tff(addCaseBooleanConditionEqualRanges1_6,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v925(VarNext)
       => ( v6(VarNext,0)
        <=> v6(VarCurr,0) ) ) ) ).

tff(addCaseBooleanConditionEqualRanges0_8,axiom,
    ! [VarNext: state_type] :
      ( v925(VarNext)
     => ( v6(VarNext,0)
      <=> v935(VarNext) ) ) ).

tff(addAssignment_236,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v935(VarNext)
      <=> v933(VarCurr) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_40,axiom,
    ! [VarCurr: state_type] :
      ( ~ v936(VarCurr)
     => ( v933(VarCurr)
      <=> v19(VarCurr,0) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_40,axiom,
    ! [VarCurr: state_type] :
      ( v936(VarCurr)
     => ( v933(VarCurr)
      <=> $true ) ) ).

tff(writeUnaryOperator_100,axiom,
    ! [VarCurr: state_type] :
      ( ~ v936(VarCurr)
    <=> v8(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_158,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v925(VarNext)
      <=> v926(VarNext) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_157,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v926(VarNext)
      <=> ( v927(VarNext)
          & v788(VarNext) ) ) ) ).

tff(writeUnaryOperator_99,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v927(VarNext)
      <=> v929(VarNext) ) ) ).

tff(addAssignment_235,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v929(VarNext)
      <=> v788(VarCurr) ) ) ).

tff(addConditionBooleanCondShiftedRangesElseBranch,axiom,
    ! [VarCurr: state_type] :
      ( ~ v917(VarCurr)
     => ( v19(VarCurr,1)
      <=> $false ) ) ).

tff(addConditionBooleanCondShiftedRangesThenBranch,axiom,
    ! [VarCurr: state_type] :
      ( v917(VarCurr)
     => ( v19(VarCurr,1)
      <=> v921(VarCurr) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_17,axiom,
    ! [VarCurr: state_type] :
      ( ~ v918(VarCurr)
     => ( v921(VarCurr)
      <=> v922(VarCurr) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_16,axiom,
    ! [VarCurr: state_type] :
      ( v918(VarCurr)
     => ( v921(VarCurr)
      <=> $true ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_39,axiom,
    ! [VarCurr: state_type] :
      ( ~ v705(VarCurr)
     => ( v922(VarCurr)
      <=> $true ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_39,axiom,
    ! [VarCurr: state_type] :
      ( v705(VarCurr)
     => ( v922(VarCurr)
      <=> $true ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_156,axiom,
    ! [VarCurr: state_type] :
      ( v917(VarCurr)
    <=> ( v918(VarCurr)
        | v919(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_155,axiom,
    ! [VarCurr: state_type] :
      ( v919(VarCurr)
    <=> ( v920(VarCurr)
        & v696(VarCurr) ) ) ).

tff(writeUnaryOperator_98,axiom,
    ! [VarCurr: state_type] :
      ( ~ v920(VarCurr)
    <=> v703(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_154,axiom,
    ! [VarCurr: state_type] :
      ( v918(VarCurr)
    <=> ( v699(VarCurr)
        & v695(VarCurr) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_38,axiom,
    ! [VarCurr: state_type] :
      ( ~ v910(VarCurr)
     => ( v19(VarCurr,0)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_38,axiom,
    ! [VarCurr: state_type] :
      ( v910(VarCurr)
     => ( v19(VarCurr,0)
      <=> v914(VarCurr) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_16,axiom,
    ! [VarCurr: state_type] :
      ( ~ v911(VarCurr)
     => ( v914(VarCurr)
      <=> $true ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_15,axiom,
    ! [VarCurr: state_type] :
      ( v911(VarCurr)
     => ( v914(VarCurr)
      <=> v915(VarCurr) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_37,axiom,
    ! [VarCurr: state_type] :
      ( ~ v701(VarCurr)
     => ( v915(VarCurr)
      <=> $true ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_37,axiom,
    ! [VarCurr: state_type] :
      ( v701(VarCurr)
     => ( v915(VarCurr)
      <=> $true ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_153,axiom,
    ! [VarCurr: state_type] :
      ( v910(VarCurr)
    <=> ( v911(VarCurr)
        | v913(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_152,axiom,
    ! [VarCurr: state_type] :
      ( v913(VarCurr)
    <=> ( v703(VarCurr)
        & v696(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_151,axiom,
    ! [VarCurr: state_type] :
      ( v911(VarCurr)
    <=> ( v912(VarCurr)
        & v695(VarCurr) ) ) ).

tff(writeUnaryOperator_97,axiom,
    ! [VarCurr: state_type] :
      ( ~ v912(VarCurr)
    <=> v699(VarCurr) ) ).

tff(addAssignment_234,axiom,
    ! [VarCurr: state_type] :
      ( v21(VarCurr)
    <=> v23(VarCurr) ) ).

tff(addBitVectorEqualityBitBlasted_46,axiom,
    ! [VarCurr: state_type] :
      ( v23(VarCurr)
    <=> ( ( v25(VarCurr,4)
        <=> $false )
        & ( v25(VarCurr,3)
        <=> $false )
        & ( v25(VarCurr,2)
        <=> $false )
        & ( v25(VarCurr,1)
        <=> $false )
        & ( v25(VarCurr,0)
        <=> $false ) ) ) ).

tff(addCaseBooleanConditionEqualRanges1_5,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v894(VarNext)
       => ! [B: $int] :
            ( ( $less(B,5)
              & ~ $less(B,0) )
           => ( v25(VarNext,B)
            <=> v25(VarCurr,B) ) ) ) ) ).

tff(addCaseBooleanConditionEqualRanges0_7,axiom,
    ! [VarNext: state_type] :
      ( v894(VarNext)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v25(VarNext,B)
          <=> v904(VarNext,B) ) ) ) ).

tff(addAssignment_233,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v904(VarNext,B)
          <=> v902(VarCurr,B) ) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_36,axiom,
    ! [VarCurr: state_type] :
      ( ~ v905(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v902(VarCurr,B)
          <=> v30(VarCurr,B) ) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_36,axiom,
    ! [VarCurr: state_type] :
      ( v905(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v902(VarCurr,B)
          <=> $false ) ) ) ).

tff(writeUnaryOperator_96,axiom,
    ! [VarCurr: state_type] :
      ( ~ v905(VarCurr)
    <=> v27(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_150,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v894(VarNext)
      <=> v895(VarNext) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_149,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v895(VarNext)
      <=> ( v896(VarNext)
          & v891(VarNext) ) ) ) ).

tff(writeUnaryOperator_95,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v896(VarNext)
      <=> v898(VarNext) ) ) ).

tff(addAssignment_232,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v898(VarNext)
      <=> v891(VarCurr) ) ) ).

tff(addAssignment_231,axiom,
    ! [VarCurr: state_type] :
      ( v891(VarCurr)
    <=> v788(VarCurr) ) ).

tff(addParallelCaseBooleanConditionEqualRanges3_4,axiom,
    ! [VarCurr: state_type] :
      ( ( ~ v816(VarCurr)
        & ~ v818(VarCurr)
        & ~ v859(VarCurr) )
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v30(VarCurr,B)
          <=> v25(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges2_7,axiom,
    ! [VarCurr: state_type] :
      ( v859(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v30(VarCurr,B)
          <=> v861(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_15,axiom,
    ! [VarCurr: state_type] :
      ( v818(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v30(VarCurr,B)
          <=> v820(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_14,axiom,
    ! [VarCurr: state_type] :
      ( v816(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v30(VarCurr,B)
          <=> v25(VarCurr,B) ) ) ) ).

tff(addBitVectorEqualityBitBlasted_45,axiom,
    ! [VarCurr: state_type] :
      ( v888(VarCurr)
    <=> ( ( v889(VarCurr,1)
        <=> $true )
        & ( v889(VarCurr,0)
        <=> $true ) ) ) ).

tff(addAssignment_230,axiom,
    ! [VarCurr: state_type] :
      ( v889(VarCurr,0)
    <=> v56(VarCurr) ) ).

tff(addAssignment_229,axiom,
    ! [VarCurr: state_type] :
      ( v889(VarCurr,1)
    <=> v32(VarCurr) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_35,axiom,
    ! [VarCurr: state_type] :
      ( ~ v862(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v861(VarCurr,B)
          <=> v863(VarCurr,B) ) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_35,axiom,
    ! [VarCurr: state_type] :
      ( v862(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v861(VarCurr,B)
          <=> b01111(B) ) ) ) ).

tff(addAssignment_228,axiom,
    ! [VarCurr: state_type] :
      ( v863(VarCurr,0)
    <=> v885(VarCurr) ) ).

tff(addAssignment_227,axiom,
    ! [VarCurr: state_type] :
      ( v863(VarCurr,1)
    <=> v883(VarCurr) ) ).

tff(addAssignment_226,axiom,
    ! [VarCurr: state_type] :
      ( v863(VarCurr,2)
    <=> v878(VarCurr) ) ).

tff(addAssignment_225,axiom,
    ! [VarCurr: state_type] :
      ( v863(VarCurr,3)
    <=> v873(VarCurr) ) ).

tff(addAssignment_224,axiom,
    ! [VarCurr: state_type] :
      ( v863(VarCurr,4)
    <=> v865(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_148,axiom,
    ! [VarCurr: state_type] :
      ( v883(VarCurr)
    <=> ( v884(VarCurr)
        & v887(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_68,axiom,
    ! [VarCurr: state_type] :
      ( v887(VarCurr)
    <=> ( v25(VarCurr,0)
        | v25(VarCurr,1) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_147,axiom,
    ! [VarCurr: state_type] :
      ( v884(VarCurr)
    <=> ( v885(VarCurr)
        | v886(VarCurr) ) ) ).

tff(writeUnaryOperator_94,axiom,
    ! [VarCurr: state_type] :
      ( ~ v886(VarCurr)
    <=> v25(VarCurr,1) ) ).

tff(writeUnaryOperator_93,axiom,
    ! [VarCurr: state_type] :
      ( ~ v885(VarCurr)
    <=> v25(VarCurr,0) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_146,axiom,
    ! [VarCurr: state_type] :
      ( v878(VarCurr)
    <=> ( v879(VarCurr)
        & v882(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_67,axiom,
    ! [VarCurr: state_type] :
      ( v882(VarCurr)
    <=> ( v870(VarCurr)
        | v25(VarCurr,2) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_145,axiom,
    ! [VarCurr: state_type] :
      ( v879(VarCurr)
    <=> ( v880(VarCurr)
        | v881(VarCurr) ) ) ).

tff(writeUnaryOperator_92,axiom,
    ! [VarCurr: state_type] :
      ( ~ v881(VarCurr)
    <=> v25(VarCurr,2) ) ).

tff(writeUnaryOperator_91,axiom,
    ! [VarCurr: state_type] :
      ( ~ v880(VarCurr)
    <=> v870(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_144,axiom,
    ! [VarCurr: state_type] :
      ( v873(VarCurr)
    <=> ( v874(VarCurr)
        & v877(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_66,axiom,
    ! [VarCurr: state_type] :
      ( v877(VarCurr)
    <=> ( v869(VarCurr)
        | v25(VarCurr,3) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_143,axiom,
    ! [VarCurr: state_type] :
      ( v874(VarCurr)
    <=> ( v875(VarCurr)
        | v876(VarCurr) ) ) ).

tff(writeUnaryOperator_90,axiom,
    ! [VarCurr: state_type] :
      ( ~ v876(VarCurr)
    <=> v25(VarCurr,3) ) ).

tff(writeUnaryOperator_89,axiom,
    ! [VarCurr: state_type] :
      ( ~ v875(VarCurr)
    <=> v869(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_142,axiom,
    ! [VarCurr: state_type] :
      ( v865(VarCurr)
    <=> ( v866(VarCurr)
        & v872(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_65,axiom,
    ! [VarCurr: state_type] :
      ( v872(VarCurr)
    <=> ( v868(VarCurr)
        | v25(VarCurr,4) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_141,axiom,
    ! [VarCurr: state_type] :
      ( v866(VarCurr)
    <=> ( v867(VarCurr)
        | v871(VarCurr) ) ) ).

tff(writeUnaryOperator_88,axiom,
    ! [VarCurr: state_type] :
      ( ~ v871(VarCurr)
    <=> v25(VarCurr,4) ) ).

tff(writeUnaryOperator_87,axiom,
    ! [VarCurr: state_type] :
      ( ~ v867(VarCurr)
    <=> v868(VarCurr) ) ).

tff(writeBinaryOperatorShiftedRanges_64,axiom,
    ! [VarCurr: state_type] :
      ( v868(VarCurr)
    <=> ( v869(VarCurr)
        & v25(VarCurr,3) ) ) ).

tff(writeBinaryOperatorShiftedRanges_63,axiom,
    ! [VarCurr: state_type] :
      ( v869(VarCurr)
    <=> ( v870(VarCurr)
        & v25(VarCurr,2) ) ) ).

tff(writeBinaryOperatorShiftedRanges_62,axiom,
    ! [VarCurr: state_type] :
      ( v870(VarCurr)
    <=> ( v25(VarCurr,0)
        & v25(VarCurr,1) ) ) ).

tff(addBitVectorEqualityBitBlasted_44,axiom,
    ! [VarCurr: state_type] :
      ( v862(VarCurr)
    <=> ( ( v25(VarCurr,4)
        <=> $false )
        & ( v25(VarCurr,3)
        <=> $true )
        & ( v25(VarCurr,2)
        <=> $true )
        & ( v25(VarCurr,1)
        <=> $true )
        & ( v25(VarCurr,0)
        <=> $true ) ) ) ).

tff(addBitVectorEqualityBitBlasted_43,axiom,
    ! [VarCurr: state_type] :
      ( v859(VarCurr)
    <=> ( ( v860(VarCurr,1)
        <=> $true )
        & ( v860(VarCurr,0)
        <=> $false ) ) ) ).

tff(addAssignment_223,axiom,
    ! [VarCurr: state_type] :
      ( v860(VarCurr,0)
    <=> v56(VarCurr) ) ).

tff(addAssignment_222,axiom,
    ! [VarCurr: state_type] :
      ( v860(VarCurr,1)
    <=> v32(VarCurr) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_34,axiom,
    ! [VarCurr: state_type] :
      ( ~ v821(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,32)
            & ~ $less(B,0) )
         => ( v820(VarCurr,B)
          <=> v822(VarCurr,B) ) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_34,axiom,
    ! [VarCurr: state_type] :
      ( v821(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,32)
            & ~ $less(B,0) )
         => ( v820(VarCurr,B)
          <=> $false ) ) ) ).

tff(addSignExtensionConstraint_79,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,6)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_78,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,7)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_77,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,8)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_76,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,9)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_75,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,10)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_74,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,11)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_73,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,12)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_72,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,13)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_71,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,14)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_70,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,15)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_69,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,16)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_68,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,17)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_67,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,18)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_66,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,19)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_65,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,20)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_64,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,21)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_63,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,22)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_62,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,23)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_61,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,24)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_60,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,25)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_59,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,26)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_58,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,27)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_57,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,28)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_56,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,29)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_55,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,30)
    <=> v823(VarCurr,5) ) ).

tff(addSignExtensionConstraint_54,axiom,
    ! [VarCurr: state_type] :
      ( v822(VarCurr,31)
    <=> v823(VarCurr,5) ) ).

tff(addAssignment_221,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,6)
        & ~ $less(B,0) )
     => ( v822(VarCurr,B)
      <=> v823(VarCurr,B) ) ) ).

tff(addAssignment_220,axiom,
    ! [VarCurr: state_type] :
      ( v823(VarCurr,0)
    <=> v857(VarCurr) ) ).

tff(addAssignment_219,axiom,
    ! [VarCurr: state_type] :
      ( v823(VarCurr,1)
    <=> v855(VarCurr) ) ).

tff(addAssignment_218,axiom,
    ! [VarCurr: state_type] :
      ( v823(VarCurr,2)
    <=> v851(VarCurr) ) ).

tff(addAssignment_217,axiom,
    ! [VarCurr: state_type] :
      ( v823(VarCurr,3)
    <=> v847(VarCurr) ) ).

tff(addAssignment_216,axiom,
    ! [VarCurr: state_type] :
      ( v823(VarCurr,4)
    <=> v843(VarCurr) ) ).

tff(addAssignment_215,axiom,
    ! [VarCurr: state_type] :
      ( v823(VarCurr,5)
    <=> v825(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_140,axiom,
    ! [VarCurr: state_type] :
      ( v855(VarCurr)
    <=> ( v856(VarCurr)
        & v858(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_139,axiom,
    ! [VarCurr: state_type] :
      ( v858(VarCurr)
    <=> ( v829(VarCurr,0)
        | v837(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_61,axiom,
    ! [VarCurr: state_type] :
      ( v856(VarCurr)
    <=> ( v857(VarCurr)
        | v829(VarCurr,1) ) ) ).

tff(writeUnaryOperator_86,axiom,
    ! [VarCurr: state_type] :
      ( ~ v857(VarCurr)
    <=> v829(VarCurr,0) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_138,axiom,
    ! [VarCurr: state_type] :
      ( v851(VarCurr)
    <=> ( v852(VarCurr)
        & v854(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_137,axiom,
    ! [VarCurr: state_type] :
      ( v854(VarCurr)
    <=> ( v835(VarCurr)
        | v838(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_60,axiom,
    ! [VarCurr: state_type] :
      ( v852(VarCurr)
    <=> ( v853(VarCurr)
        | v829(VarCurr,2) ) ) ).

tff(writeUnaryOperator_85,axiom,
    ! [VarCurr: state_type] :
      ( ~ v853(VarCurr)
    <=> v835(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_136,axiom,
    ! [VarCurr: state_type] :
      ( v847(VarCurr)
    <=> ( v848(VarCurr)
        & v850(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_135,axiom,
    ! [VarCurr: state_type] :
      ( v850(VarCurr)
    <=> ( v833(VarCurr)
        | v839(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_59,axiom,
    ! [VarCurr: state_type] :
      ( v848(VarCurr)
    <=> ( v849(VarCurr)
        | v829(VarCurr,3) ) ) ).

tff(writeUnaryOperator_84,axiom,
    ! [VarCurr: state_type] :
      ( ~ v849(VarCurr)
    <=> v833(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_134,axiom,
    ! [VarCurr: state_type] :
      ( v843(VarCurr)
    <=> ( v844(VarCurr)
        & v846(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_133,axiom,
    ! [VarCurr: state_type] :
      ( v846(VarCurr)
    <=> ( v831(VarCurr)
        | v840(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_58,axiom,
    ! [VarCurr: state_type] :
      ( v844(VarCurr)
    <=> ( v845(VarCurr)
        | v829(VarCurr,4) ) ) ).

tff(writeUnaryOperator_83,axiom,
    ! [VarCurr: state_type] :
      ( ~ v845(VarCurr)
    <=> v831(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_132,axiom,
    ! [VarCurr: state_type] :
      ( v825(VarCurr)
    <=> ( v826(VarCurr)
        & v841(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_131,axiom,
    ! [VarCurr: state_type] :
      ( v841(VarCurr)
    <=> ( v828(VarCurr)
        | v842(VarCurr) ) ) ).

tff(writeUnaryOperator_82,axiom,
    ! [VarCurr: state_type] :
      ( ~ v842(VarCurr)
    <=> v829(VarCurr,5) ) ).

tff(writeBinaryOperatorShiftedRanges_57,axiom,
    ! [VarCurr: state_type] :
      ( v826(VarCurr)
    <=> ( v827(VarCurr)
        | v829(VarCurr,5) ) ) ).

tff(writeUnaryOperator_81,axiom,
    ! [VarCurr: state_type] :
      ( ~ v827(VarCurr)
    <=> v828(VarCurr) ) ).

tff(writeBinaryOperatorShiftedRanges_56,axiom,
    ! [VarCurr: state_type] :
      ( v828(VarCurr)
    <=> ( v829(VarCurr,4)
        | v830(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_130,axiom,
    ! [VarCurr: state_type] :
      ( v830(VarCurr)
    <=> ( v831(VarCurr)
        & v840(VarCurr) ) ) ).

tff(writeUnaryOperator_80,axiom,
    ! [VarCurr: state_type] :
      ( ~ v840(VarCurr)
    <=> v829(VarCurr,4) ) ).

tff(writeBinaryOperatorShiftedRanges_55,axiom,
    ! [VarCurr: state_type] :
      ( v831(VarCurr)
    <=> ( v829(VarCurr,3)
        | v832(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_129,axiom,
    ! [VarCurr: state_type] :
      ( v832(VarCurr)
    <=> ( v833(VarCurr)
        & v839(VarCurr) ) ) ).

tff(writeUnaryOperator_79,axiom,
    ! [VarCurr: state_type] :
      ( ~ v839(VarCurr)
    <=> v829(VarCurr,3) ) ).

tff(writeBinaryOperatorShiftedRanges_54,axiom,
    ! [VarCurr: state_type] :
      ( v833(VarCurr)
    <=> ( v829(VarCurr,2)
        | v834(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_128,axiom,
    ! [VarCurr: state_type] :
      ( v834(VarCurr)
    <=> ( v835(VarCurr)
        & v838(VarCurr) ) ) ).

tff(writeUnaryOperator_78,axiom,
    ! [VarCurr: state_type] :
      ( ~ v838(VarCurr)
    <=> v829(VarCurr,2) ) ).

tff(writeBinaryOperatorShiftedRanges_53,axiom,
    ! [VarCurr: state_type] :
      ( v835(VarCurr)
    <=> ( v829(VarCurr,1)
        | v836(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_127,axiom,
    ! [VarCurr: state_type] :
      ( v836(VarCurr)
    <=> ( v829(VarCurr,0)
        & v837(VarCurr) ) ) ).

tff(writeUnaryOperator_77,axiom,
    ! [VarCurr: state_type] :
      ( ~ v837(VarCurr)
    <=> v829(VarCurr,1) ) ).

tff(addZeroExtensionConstraint_2,axiom,
    ! [VarCurr: state_type] : ~ v829(VarCurr,5) ).

tff(addAssignment_214,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,5)
        & ~ $less(B,0) )
     => ( v829(VarCurr,B)
      <=> v25(VarCurr,B) ) ) ).

tff(addBitVectorEqualityBitBlasted_42,axiom,
    ! [VarCurr: state_type] :
      ( v821(VarCurr)
    <=> ( ( v25(VarCurr,4)
        <=> $false )
        & ( v25(VarCurr,3)
        <=> $false )
        & ( v25(VarCurr,2)
        <=> $false )
        & ( v25(VarCurr,1)
        <=> $false )
        & ( v25(VarCurr,0)
        <=> $false ) ) ) ).

tff(addBitVectorEqualityBitBlasted_41,axiom,
    ! [VarCurr: state_type] :
      ( v818(VarCurr)
    <=> ( ( v819(VarCurr,1)
        <=> $false )
        & ( v819(VarCurr,0)
        <=> $true ) ) ) ).

tff(addAssignment_213,axiom,
    ! [VarCurr: state_type] :
      ( v819(VarCurr,0)
    <=> v56(VarCurr) ) ).

tff(addAssignment_212,axiom,
    ! [VarCurr: state_type] :
      ( v819(VarCurr,1)
    <=> v32(VarCurr) ) ).

tff(addAssignmentInitValueVector_3,axiom,
    ! [B: $int] :
      ( ( $less(B,5)
        & ~ $less(B,0) )
     => ( v25(constB0,B)
      <=> $false ) ) ).

tff(addBitVectorEqualityBitBlasted_40,axiom,
    ! [VarCurr: state_type] :
      ( v816(VarCurr)
    <=> ( ( v817(VarCurr,1)
        <=> $false )
        & ( v817(VarCurr,0)
        <=> $false ) ) ) ).

tff(addAssignment_211,axiom,
    ! [VarCurr: state_type] :
      ( v817(VarCurr,0)
    <=> v56(VarCurr) ) ).

tff(addAssignment_210,axiom,
    ! [VarCurr: state_type] :
      ( v817(VarCurr,1)
    <=> v32(VarCurr) ) ).

tff(addAssignment_209,axiom,
    ! [VarCurr: state_type] :
      ( v56(VarCurr)
    <=> v58(VarCurr) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_33,axiom,
    ! [VarCurr: state_type] :
      ( ~ v809(VarCurr)
     => ( v58(VarCurr)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_33,axiom,
    ! [VarCurr: state_type] :
      ( v809(VarCurr)
     => ( v58(VarCurr)
      <=> v810(VarCurr) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_14,axiom,
    ! [VarCurr: state_type] :
      ( ~ v695(VarCurr)
     => ( v810(VarCurr)
      <=> v813(VarCurr) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_13,axiom,
    ! [VarCurr: state_type] :
      ( v695(VarCurr)
     => ( v810(VarCurr)
      <=> v811(VarCurr) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_32,axiom,
    ! [VarCurr: state_type] :
      ( ~ v703(VarCurr)
     => ( v813(VarCurr)
      <=> v814(VarCurr) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_32,axiom,
    ! [VarCurr: state_type] :
      ( v703(VarCurr)
     => ( v813(VarCurr)
      <=> $false ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_31,axiom,
    ! [VarCurr: state_type] :
      ( ~ v705(VarCurr)
     => ( v814(VarCurr)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_31,axiom,
    ! [VarCurr: state_type] :
      ( v705(VarCurr)
     => ( v814(VarCurr)
      <=> $true ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_30,axiom,
    ! [VarCurr: state_type] :
      ( ~ v699(VarCurr)
     => ( v811(VarCurr)
      <=> v812(VarCurr) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_30,axiom,
    ! [VarCurr: state_type] :
      ( v699(VarCurr)
     => ( v811(VarCurr)
      <=> $true ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_29,axiom,
    ! [VarCurr: state_type] :
      ( ~ v701(VarCurr)
     => ( v812(VarCurr)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_29,axiom,
    ! [VarCurr: state_type] :
      ( v701(VarCurr)
     => ( v812(VarCurr)
      <=> $false ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_126,axiom,
    ! [VarCurr: state_type] :
      ( v809(VarCurr)
    <=> ( v695(VarCurr)
        | v696(VarCurr) ) ) ).

tff(addAssignment_208,axiom,
    ! [VarCurr: state_type] :
      ( v60(VarCurr)
    <=> v62(VarCurr) ) ).

tff(addBitVectorEqualityBitBlasted_39,axiom,
    ! [VarCurr: state_type] :
      ( v62(VarCurr)
    <=> ( ( v64(VarCurr,4)
        <=> $false )
        & ( v64(VarCurr,3)
        <=> $false )
        & ( v64(VarCurr,2)
        <=> $false )
        & ( v64(VarCurr,1)
        <=> $false )
        & ( v64(VarCurr,0)
        <=> $false ) ) ) ).

tff(addCaseBooleanConditionEqualRanges1_4,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v793(VarNext)
       => ! [B: $int] :
            ( ( $less(B,5)
              & ~ $less(B,0) )
           => ( v64(VarNext,B)
            <=> v64(VarCurr,B) ) ) ) ) ).

tff(addCaseBooleanConditionEqualRanges0_6,axiom,
    ! [VarNext: state_type] :
      ( v793(VarNext)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v64(VarNext,B)
          <=> v803(VarNext,B) ) ) ) ).

tff(addAssignment_207,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v803(VarNext,B)
          <=> v801(VarCurr,B) ) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_28,axiom,
    ! [VarCurr: state_type] :
      ( ~ v804(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v801(VarCurr,B)
          <=> v68(VarCurr,B) ) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_28,axiom,
    ! [VarCurr: state_type] :
      ( v804(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v801(VarCurr,B)
          <=> $false ) ) ) ).

tff(writeUnaryOperator_76,axiom,
    ! [VarCurr: state_type] :
      ( ~ v804(VarCurr)
    <=> v66(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_125,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v793(VarNext)
      <=> v794(VarNext) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_124,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v794(VarNext)
      <=> ( v795(VarNext)
          & v786(VarNext) ) ) ) ).

tff(writeUnaryOperator_75,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v795(VarNext)
      <=> v797(VarNext) ) ) ).

tff(addAssignment_206,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v797(VarNext)
      <=> v786(VarCurr) ) ) ).

tff(addAssignment_205,axiom,
    ! [VarCurr: state_type] :
      ( v786(VarCurr)
    <=> v788(VarCurr) ) ).

tff(addAssignment_204,axiom,
    ! [VarCurr: state_type] :
      ( v788(VarCurr)
    <=> v790(VarCurr) ) ).

tff(addAssignment_203,axiom,
    ! [VarCurr: state_type] :
      ( v790(VarCurr)
    <=> v332(VarCurr) ) ).

tff(addParallelCaseBooleanConditionEqualRanges3_3,axiom,
    ! [VarCurr: state_type] :
      ( ( ~ v710(VarCurr)
        & ~ v712(VarCurr)
        & ~ v754(VarCurr) )
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v68(VarCurr,B)
          <=> v64(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges2_6,axiom,
    ! [VarCurr: state_type] :
      ( v754(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v68(VarCurr,B)
          <=> v756(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_13,axiom,
    ! [VarCurr: state_type] :
      ( v712(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v68(VarCurr,B)
          <=> v714(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_12,axiom,
    ! [VarCurr: state_type] :
      ( v710(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v68(VarCurr,B)
          <=> v64(VarCurr,B) ) ) ) ).

tff(addBitVectorEqualityBitBlasted_38,axiom,
    ! [VarCurr: state_type] :
      ( v783(VarCurr)
    <=> ( ( v784(VarCurr,1)
        <=> $true )
        & ( v784(VarCurr,0)
        <=> $true ) ) ) ).

tff(addAssignment_202,axiom,
    ! [VarCurr: state_type] :
      ( v784(VarCurr,0)
    <=> v690(VarCurr) ) ).

tff(addAssignment_201,axiom,
    ! [VarCurr: state_type] :
      ( v784(VarCurr,1)
    <=> v70(VarCurr) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_27,axiom,
    ! [VarCurr: state_type] :
      ( ~ v757(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v756(VarCurr,B)
          <=> v758(VarCurr,B) ) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_27,axiom,
    ! [VarCurr: state_type] :
      ( v757(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,5)
            & ~ $less(B,0) )
         => ( v756(VarCurr,B)
          <=> b01111(B) ) ) ) ).

tff(addAssignment_200,axiom,
    ! [VarCurr: state_type] :
      ( v758(VarCurr,0)
    <=> v780(VarCurr) ) ).

tff(addAssignment_199,axiom,
    ! [VarCurr: state_type] :
      ( v758(VarCurr,1)
    <=> v778(VarCurr) ) ).

tff(addAssignment_198,axiom,
    ! [VarCurr: state_type] :
      ( v758(VarCurr,2)
    <=> v773(VarCurr) ) ).

tff(addAssignment_197,axiom,
    ! [VarCurr: state_type] :
      ( v758(VarCurr,3)
    <=> v768(VarCurr) ) ).

tff(addAssignment_196,axiom,
    ! [VarCurr: state_type] :
      ( v758(VarCurr,4)
    <=> v760(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_123,axiom,
    ! [VarCurr: state_type] :
      ( v778(VarCurr)
    <=> ( v779(VarCurr)
        & v782(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_52,axiom,
    ! [VarCurr: state_type] :
      ( v782(VarCurr)
    <=> ( v64(VarCurr,0)
        | v64(VarCurr,1) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_122,axiom,
    ! [VarCurr: state_type] :
      ( v779(VarCurr)
    <=> ( v780(VarCurr)
        | v781(VarCurr) ) ) ).

tff(writeUnaryOperator_74,axiom,
    ! [VarCurr: state_type] :
      ( ~ v781(VarCurr)
    <=> v64(VarCurr,1) ) ).

tff(writeUnaryOperator_73,axiom,
    ! [VarCurr: state_type] :
      ( ~ v780(VarCurr)
    <=> v64(VarCurr,0) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_121,axiom,
    ! [VarCurr: state_type] :
      ( v773(VarCurr)
    <=> ( v774(VarCurr)
        & v777(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_51,axiom,
    ! [VarCurr: state_type] :
      ( v777(VarCurr)
    <=> ( v765(VarCurr)
        | v64(VarCurr,2) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_120,axiom,
    ! [VarCurr: state_type] :
      ( v774(VarCurr)
    <=> ( v775(VarCurr)
        | v776(VarCurr) ) ) ).

tff(writeUnaryOperator_72,axiom,
    ! [VarCurr: state_type] :
      ( ~ v776(VarCurr)
    <=> v64(VarCurr,2) ) ).

tff(writeUnaryOperator_71,axiom,
    ! [VarCurr: state_type] :
      ( ~ v775(VarCurr)
    <=> v765(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_119,axiom,
    ! [VarCurr: state_type] :
      ( v768(VarCurr)
    <=> ( v769(VarCurr)
        & v772(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_50,axiom,
    ! [VarCurr: state_type] :
      ( v772(VarCurr)
    <=> ( v764(VarCurr)
        | v64(VarCurr,3) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_118,axiom,
    ! [VarCurr: state_type] :
      ( v769(VarCurr)
    <=> ( v770(VarCurr)
        | v771(VarCurr) ) ) ).

tff(writeUnaryOperator_70,axiom,
    ! [VarCurr: state_type] :
      ( ~ v771(VarCurr)
    <=> v64(VarCurr,3) ) ).

tff(writeUnaryOperator_69,axiom,
    ! [VarCurr: state_type] :
      ( ~ v770(VarCurr)
    <=> v764(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_117,axiom,
    ! [VarCurr: state_type] :
      ( v760(VarCurr)
    <=> ( v761(VarCurr)
        & v767(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_49,axiom,
    ! [VarCurr: state_type] :
      ( v767(VarCurr)
    <=> ( v763(VarCurr)
        | v64(VarCurr,4) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_116,axiom,
    ! [VarCurr: state_type] :
      ( v761(VarCurr)
    <=> ( v762(VarCurr)
        | v766(VarCurr) ) ) ).

tff(writeUnaryOperator_68,axiom,
    ! [VarCurr: state_type] :
      ( ~ v766(VarCurr)
    <=> v64(VarCurr,4) ) ).

tff(writeUnaryOperator_67,axiom,
    ! [VarCurr: state_type] :
      ( ~ v762(VarCurr)
    <=> v763(VarCurr) ) ).

tff(writeBinaryOperatorShiftedRanges_48,axiom,
    ! [VarCurr: state_type] :
      ( v763(VarCurr)
    <=> ( v764(VarCurr)
        & v64(VarCurr,3) ) ) ).

tff(writeBinaryOperatorShiftedRanges_47,axiom,
    ! [VarCurr: state_type] :
      ( v764(VarCurr)
    <=> ( v765(VarCurr)
        & v64(VarCurr,2) ) ) ).

tff(writeBinaryOperatorShiftedRanges_46,axiom,
    ! [VarCurr: state_type] :
      ( v765(VarCurr)
    <=> ( v64(VarCurr,0)
        & v64(VarCurr,1) ) ) ).

tff(addBitVectorEqualityBitBlasted_37,axiom,
    ! [VarCurr: state_type] :
      ( v757(VarCurr)
    <=> ( ( v64(VarCurr,4)
        <=> $false )
        & ( v64(VarCurr,3)
        <=> $true )
        & ( v64(VarCurr,2)
        <=> $true )
        & ( v64(VarCurr,1)
        <=> $true )
        & ( v64(VarCurr,0)
        <=> $true ) ) ) ).

tff(bitBlastConstant_192,axiom,
    ~ b01111(4) ).

tff(bitBlastConstant_191,axiom,
    b01111(3) ).

tff(bitBlastConstant_190,axiom,
    b01111(2) ).

tff(bitBlastConstant_189,axiom,
    b01111(1) ).

tff(bitBlastConstant_188,axiom,
    b01111(0) ).

tff(addBitVectorEqualityBitBlasted_36,axiom,
    ! [VarCurr: state_type] :
      ( v754(VarCurr)
    <=> ( ( v755(VarCurr,1)
        <=> $true )
        & ( v755(VarCurr,0)
        <=> $false ) ) ) ).

tff(addAssignment_195,axiom,
    ! [VarCurr: state_type] :
      ( v755(VarCurr,0)
    <=> v690(VarCurr) ) ).

tff(addAssignment_194,axiom,
    ! [VarCurr: state_type] :
      ( v755(VarCurr,1)
    <=> v70(VarCurr) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_26,axiom,
    ! [VarCurr: state_type] :
      ( ~ v715(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,32)
            & ~ $less(B,0) )
         => ( v714(VarCurr,B)
          <=> v716(VarCurr,B) ) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_26,axiom,
    ! [VarCurr: state_type] :
      ( v715(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,32)
            & ~ $less(B,0) )
         => ( v714(VarCurr,B)
          <=> $false ) ) ) ).

tff(addSignExtensionConstraint_53,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,6)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_52,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,7)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_51,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,8)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_50,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,9)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_49,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,10)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_48,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,11)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_47,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,12)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_46,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,13)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_45,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,14)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_44,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,15)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_43,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,16)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_42,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,17)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_41,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,18)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_40,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,19)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_39,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,20)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_38,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,21)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_37,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,22)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_36,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,23)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_35,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,24)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_34,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,25)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_33,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,26)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_32,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,27)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_31,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,28)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_30,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,29)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_29,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,30)
    <=> v717(VarCurr,5) ) ).

tff(addSignExtensionConstraint_28,axiom,
    ! [VarCurr: state_type] :
      ( v716(VarCurr,31)
    <=> v717(VarCurr,5) ) ).

tff(addAssignment_193,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,6)
        & ~ $less(B,0) )
     => ( v716(VarCurr,B)
      <=> v717(VarCurr,B) ) ) ).

tff(addAssignment_192,axiom,
    ! [VarCurr: state_type] :
      ( v717(VarCurr,0)
    <=> v752(VarCurr) ) ).

tff(addAssignment_191,axiom,
    ! [VarCurr: state_type] :
      ( v717(VarCurr,1)
    <=> v750(VarCurr) ) ).

tff(addAssignment_190,axiom,
    ! [VarCurr: state_type] :
      ( v717(VarCurr,2)
    <=> v746(VarCurr) ) ).

tff(addAssignment_189,axiom,
    ! [VarCurr: state_type] :
      ( v717(VarCurr,3)
    <=> v742(VarCurr) ) ).

tff(addAssignment_188,axiom,
    ! [VarCurr: state_type] :
      ( v717(VarCurr,4)
    <=> v738(VarCurr) ) ).

tff(addAssignment_187,axiom,
    ! [VarCurr: state_type] :
      ( v717(VarCurr,5)
    <=> v719(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_115,axiom,
    ! [VarCurr: state_type] :
      ( v750(VarCurr)
    <=> ( v751(VarCurr)
        & v753(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_114,axiom,
    ! [VarCurr: state_type] :
      ( v753(VarCurr)
    <=> ( v723(VarCurr,0)
        | v732(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_45,axiom,
    ! [VarCurr: state_type] :
      ( v751(VarCurr)
    <=> ( v752(VarCurr)
        | v723(VarCurr,1) ) ) ).

tff(writeUnaryOperator_66,axiom,
    ! [VarCurr: state_type] :
      ( ~ v752(VarCurr)
    <=> v723(VarCurr,0) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_113,axiom,
    ! [VarCurr: state_type] :
      ( v746(VarCurr)
    <=> ( v747(VarCurr)
        & v749(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_112,axiom,
    ! [VarCurr: state_type] :
      ( v749(VarCurr)
    <=> ( v730(VarCurr)
        | v733(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_44,axiom,
    ! [VarCurr: state_type] :
      ( v747(VarCurr)
    <=> ( v748(VarCurr)
        | v723(VarCurr,2) ) ) ).

tff(writeUnaryOperator_65,axiom,
    ! [VarCurr: state_type] :
      ( ~ v748(VarCurr)
    <=> v730(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_111,axiom,
    ! [VarCurr: state_type] :
      ( v742(VarCurr)
    <=> ( v743(VarCurr)
        & v745(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_110,axiom,
    ! [VarCurr: state_type] :
      ( v745(VarCurr)
    <=> ( v728(VarCurr)
        | v734(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_43,axiom,
    ! [VarCurr: state_type] :
      ( v743(VarCurr)
    <=> ( v744(VarCurr)
        | v723(VarCurr,3) ) ) ).

tff(writeUnaryOperator_64,axiom,
    ! [VarCurr: state_type] :
      ( ~ v744(VarCurr)
    <=> v728(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_109,axiom,
    ! [VarCurr: state_type] :
      ( v738(VarCurr)
    <=> ( v739(VarCurr)
        & v741(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_108,axiom,
    ! [VarCurr: state_type] :
      ( v741(VarCurr)
    <=> ( v726(VarCurr)
        | v735(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_42,axiom,
    ! [VarCurr: state_type] :
      ( v739(VarCurr)
    <=> ( v740(VarCurr)
        | v723(VarCurr,4) ) ) ).

tff(writeUnaryOperator_63,axiom,
    ! [VarCurr: state_type] :
      ( ~ v740(VarCurr)
    <=> v726(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_107,axiom,
    ! [VarCurr: state_type] :
      ( v719(VarCurr)
    <=> ( v720(VarCurr)
        & v736(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_106,axiom,
    ! [VarCurr: state_type] :
      ( v736(VarCurr)
    <=> ( v722(VarCurr)
        | v737(VarCurr) ) ) ).

tff(writeUnaryOperator_62,axiom,
    ! [VarCurr: state_type] :
      ( ~ v737(VarCurr)
    <=> v723(VarCurr,5) ) ).

tff(writeBinaryOperatorShiftedRanges_41,axiom,
    ! [VarCurr: state_type] :
      ( v720(VarCurr)
    <=> ( v721(VarCurr)
        | v723(VarCurr,5) ) ) ).

tff(writeUnaryOperator_61,axiom,
    ! [VarCurr: state_type] :
      ( ~ v721(VarCurr)
    <=> v722(VarCurr) ) ).

tff(writeBinaryOperatorShiftedRanges_40,axiom,
    ! [VarCurr: state_type] :
      ( v722(VarCurr)
    <=> ( v723(VarCurr,4)
        | v725(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_105,axiom,
    ! [VarCurr: state_type] :
      ( v725(VarCurr)
    <=> ( v726(VarCurr)
        & v735(VarCurr) ) ) ).

tff(writeUnaryOperator_60,axiom,
    ! [VarCurr: state_type] :
      ( ~ v735(VarCurr)
    <=> v723(VarCurr,4) ) ).

tff(writeBinaryOperatorShiftedRanges_39,axiom,
    ! [VarCurr: state_type] :
      ( v726(VarCurr)
    <=> ( v723(VarCurr,3)
        | v727(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_104,axiom,
    ! [VarCurr: state_type] :
      ( v727(VarCurr)
    <=> ( v728(VarCurr)
        & v734(VarCurr) ) ) ).

tff(writeUnaryOperator_59,axiom,
    ! [VarCurr: state_type] :
      ( ~ v734(VarCurr)
    <=> v723(VarCurr,3) ) ).

tff(writeBinaryOperatorShiftedRanges_38,axiom,
    ! [VarCurr: state_type] :
      ( v728(VarCurr)
    <=> ( v723(VarCurr,2)
        | v729(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_103,axiom,
    ! [VarCurr: state_type] :
      ( v729(VarCurr)
    <=> ( v730(VarCurr)
        & v733(VarCurr) ) ) ).

tff(writeUnaryOperator_58,axiom,
    ! [VarCurr: state_type] :
      ( ~ v733(VarCurr)
    <=> v723(VarCurr,2) ) ).

tff(writeBinaryOperatorShiftedRanges_37,axiom,
    ! [VarCurr: state_type] :
      ( v730(VarCurr)
    <=> ( v723(VarCurr,1)
        | v731(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_102,axiom,
    ! [VarCurr: state_type] :
      ( v731(VarCurr)
    <=> ( v723(VarCurr,0)
        & v732(VarCurr) ) ) ).

tff(writeUnaryOperator_57,axiom,
    ! [VarCurr: state_type] :
      ( ~ v732(VarCurr)
    <=> v723(VarCurr,1) ) ).

tff(addZeroExtensionConstraint_1,axiom,
    ! [VarCurr: state_type] : ~ v723(VarCurr,5) ).

tff(addAssignment_186,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,5)
        & ~ $less(B,0) )
     => ( v723(VarCurr,B)
      <=> v64(VarCurr,B) ) ) ).

tff(addBitVectorEqualityBitBlasted_35,axiom,
    ! [VarCurr: state_type] :
      ( v715(VarCurr)
    <=> ( ( v64(VarCurr,4)
        <=> $false )
        & ( v64(VarCurr,3)
        <=> $false )
        & ( v64(VarCurr,2)
        <=> $false )
        & ( v64(VarCurr,1)
        <=> $false )
        & ( v64(VarCurr,0)
        <=> $false ) ) ) ).

tff(addBitVectorEqualityBitBlasted_34,axiom,
    ! [VarCurr: state_type] :
      ( v712(VarCurr)
    <=> ( ( v713(VarCurr,1)
        <=> $false )
        & ( v713(VarCurr,0)
        <=> $true ) ) ) ).

tff(addAssignment_185,axiom,
    ! [VarCurr: state_type] :
      ( v713(VarCurr,0)
    <=> v690(VarCurr) ) ).

tff(addAssignment_184,axiom,
    ! [VarCurr: state_type] :
      ( v713(VarCurr,1)
    <=> v70(VarCurr) ) ).

tff(addAssignmentInitValueVector_2,axiom,
    ! [B: $int] :
      ( ( $less(B,5)
        & ~ $less(B,0) )
     => ( v64(constB0,B)
      <=> $false ) ) ).

tff(bitBlastConstant_187,axiom,
    ~ b00000(4) ).

tff(bitBlastConstant_186,axiom,
    ~ b00000(3) ).

tff(bitBlastConstant_185,axiom,
    ~ b00000(2) ).

tff(bitBlastConstant_184,axiom,
    ~ b00000(1) ).

tff(bitBlastConstant_183,axiom,
    ~ b00000(0) ).

tff(addBitVectorEqualityBitBlasted_33,axiom,
    ! [VarCurr: state_type] :
      ( v710(VarCurr)
    <=> ( ( v711(VarCurr,1)
        <=> $false )
        & ( v711(VarCurr,0)
        <=> $false ) ) ) ).

tff(addAssignment_183,axiom,
    ! [VarCurr: state_type] :
      ( v711(VarCurr,0)
    <=> v690(VarCurr) ) ).

tff(addAssignment_182,axiom,
    ! [VarCurr: state_type] :
      ( v711(VarCurr,1)
    <=> v70(VarCurr) ) ).

tff(addAssignment_181,axiom,
    ! [VarCurr: state_type] :
      ( v690(VarCurr)
    <=> v692(VarCurr) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_25,axiom,
    ! [VarCurr: state_type] :
      ( ~ v694(VarCurr)
     => ( v692(VarCurr)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_25,axiom,
    ! [VarCurr: state_type] :
      ( v694(VarCurr)
     => ( v692(VarCurr)
      <=> v697(VarCurr) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_12,axiom,
    ! [VarCurr: state_type] :
      ( ~ v695(VarCurr)
     => ( v697(VarCurr)
      <=> v702(VarCurr) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_11,axiom,
    ! [VarCurr: state_type] :
      ( v695(VarCurr)
     => ( v697(VarCurr)
      <=> v698(VarCurr) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_24,axiom,
    ! [VarCurr: state_type] :
      ( ~ v703(VarCurr)
     => ( v702(VarCurr)
      <=> v704(VarCurr) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_24,axiom,
    ! [VarCurr: state_type] :
      ( v703(VarCurr)
     => ( v702(VarCurr)
      <=> $true ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_23,axiom,
    ! [VarCurr: state_type] :
      ( ~ v705(VarCurr)
     => ( v704(VarCurr)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_23,axiom,
    ! [VarCurr: state_type] :
      ( v705(VarCurr)
     => ( v704(VarCurr)
      <=> $false ) ) ).

tff(writeUnaryOperator_56,axiom,
    ! [VarCurr: state_type] :
      ( ~ v705(VarCurr)
    <=> v21(VarCurr) ) ).

tff(writeUnaryOperator_55,axiom,
    ! [VarCurr: state_type] :
      ( ~ v703(VarCurr)
    <=> v60(VarCurr) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_22,axiom,
    ! [VarCurr: state_type] :
      ( ~ v699(VarCurr)
     => ( v698(VarCurr)
      <=> v700(VarCurr) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_22,axiom,
    ! [VarCurr: state_type] :
      ( v699(VarCurr)
     => ( v698(VarCurr)
      <=> $false ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_21,axiom,
    ! [VarCurr: state_type] :
      ( ~ v701(VarCurr)
     => ( v700(VarCurr)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_21,axiom,
    ! [VarCurr: state_type] :
      ( v701(VarCurr)
     => ( v700(VarCurr)
      <=> $true ) ) ).

tff(writeUnaryOperator_54,axiom,
    ! [VarCurr: state_type] :
      ( ~ v701(VarCurr)
    <=> v60(VarCurr) ) ).

tff(writeUnaryOperator_53,axiom,
    ! [VarCurr: state_type] :
      ( ~ v699(VarCurr)
    <=> v21(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_101,axiom,
    ! [VarCurr: state_type] :
      ( v694(VarCurr)
    <=> ( v695(VarCurr)
        | v696(VarCurr) ) ) ).

tff(addBitVectorEqualityBitBlasted_32,axiom,
    ! [VarCurr: state_type] :
      ( v696(VarCurr)
    <=> ( $true
      <=> v6(VarCurr,1) ) ) ).

tff(addBitVectorEqualityBitBlasted_31,axiom,
    ! [VarCurr: state_type] :
      ( v695(VarCurr)
    <=> ( $true
      <=> v6(VarCurr,0) ) ) ).

tff(addAssignmentInitValueVector_1,axiom,
    ( v6(constB0,1)
  <=> $false ) ).

tff(addAssignmentInitValueVector,axiom,
    ( v6(constB0,0)
  <=> $true ) ).

tff(addAssignment_180,axiom,
    ! [VarCurr: state_type] :
      ( v70(VarCurr)
    <=> v72(VarCurr) ) ).

tff(addAssignment_179,axiom,
    ! [VarCurr: state_type] :
      ( v72(VarCurr)
    <=> v74(VarCurr) ) ).

tff(addAssignment_178,axiom,
    ! [VarCurr: state_type] :
      ( v74(VarCurr)
    <=> v76(VarCurr) ) ).

tff(addAssignment_177,axiom,
    ! [VarCurr: state_type] :
      ( v76(VarCurr)
    <=> v78(VarCurr) ) ).

tff(addAssignment_176,axiom,
    ! [VarCurr: state_type] :
      ( v78(VarCurr)
    <=> v80(VarCurr) ) ).

tff(addCaseBooleanConditionEqualRanges1_3,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v677(VarNext)
       => ( v80(VarNext)
        <=> v80(VarCurr) ) ) ) ).

tff(addCaseBooleanConditionEqualRanges0_5,axiom,
    ! [VarNext: state_type] :
      ( v677(VarNext)
     => ( v80(VarNext)
      <=> v685(VarNext) ) ) ).

tff(addAssignment_175,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v685(VarNext)
      <=> v683(VarCurr) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_20,axiom,
    ! [VarCurr: state_type] :
      ( ~ v686(VarCurr)
     => ( v683(VarCurr)
      <=> v86(VarCurr) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_20,axiom,
    ! [VarCurr: state_type] :
      ( v686(VarCurr)
     => ( v683(VarCurr)
      <=> $false ) ) ).

tff(writeUnaryOperator_52,axiom,
    ! [VarCurr: state_type] :
      ( ~ v686(VarCurr)
    <=> v82(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_100,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v677(VarNext)
      <=> v678(VarNext) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_99,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v678(VarNext)
      <=> ( v679(VarNext)
          & v328(VarNext) ) ) ) ).

tff(writeUnaryOperator_51,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v679(VarNext)
      <=> v339(VarNext) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_19,axiom,
    ! [VarCurr: state_type] :
      ( ~ v669(VarCurr)
     => ( v86(VarCurr)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_19,axiom,
    ! [VarCurr: state_type] :
      ( v669(VarCurr)
     => ( v86(VarCurr)
      <=> v674(VarCurr) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_11,axiom,
    ! [VarCurr: state_type] :
      ( ~ v671(VarCurr)
     => ( v674(VarCurr)
      <=> $false ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_10,axiom,
    ! [VarCurr: state_type] :
      ( v671(VarCurr)
     => ( v674(VarCurr)
      <=> $true ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_98,axiom,
    ! [VarCurr: state_type] :
      ( v669(VarCurr)
    <=> ( v670(VarCurr)
        & v673(VarCurr) ) ) ).

tff(writeUnaryOperator_50,axiom,
    ! [VarCurr: state_type] :
      ( ~ v673(VarCurr)
    <=> v275(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_97,axiom,
    ! [VarCurr: state_type] :
      ( v670(VarCurr)
    <=> ( v671(VarCurr)
        | v672(VarCurr) ) ) ).

tff(writeUnaryOperator_49,axiom,
    ! [VarCurr: state_type] :
      ( ~ v672(VarCurr)
    <=> v272(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_96,axiom,
    ! [VarCurr: state_type] :
      ( v671(VarCurr)
    <=> ( v444(VarCurr)
        & v272(VarCurr) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_18,axiom,
    ! [VarCurr: state_type] :
      ( ~ v90(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,2)
            & ~ $less(B,0) )
         => ( v88(VarCurr,B)
          <=> v599(VarCurr,B) ) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_18,axiom,
    ! [VarCurr: state_type] :
      ( v90(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,2)
            & ~ $less(B,0) )
         => ( v88(VarCurr,B)
          <=> $false ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges4,axiom,
    ! [VarCurr: state_type] :
      ( ( ~ v600(VarCurr)
        & ~ v637(VarCurr)
        & ~ v645(VarCurr)
        & ~ v653(VarCurr) )
     => ! [B: $int] :
          ( ( $less(B,2)
            & ~ $less(B,0) )
         => ( v599(VarCurr,B)
          <=> $true ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges3_2,axiom,
    ! [VarCurr: state_type] :
      ( v653(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,2)
            & ~ $less(B,0) )
         => ( v599(VarCurr,B)
          <=> b01(B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges2_5,axiom,
    ! [VarCurr: state_type] :
      ( v645(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,2)
            & ~ $less(B,0) )
         => ( v599(VarCurr,B)
          <=> $false ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_10,axiom,
    ! [VarCurr: state_type] :
      ( v637(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,2)
            & ~ $less(B,0) )
         => ( v599(VarCurr,B)
          <=> v644(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_9,axiom,
    ! [VarCurr: state_type] :
      ( v600(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,2)
            & ~ $less(B,0) )
         => ( v599(VarCurr,B)
          <=> $false ) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_95,axiom,
    ! [VarCurr: state_type] :
      ( v653(VarCurr)
    <=> ( v655(VarCurr)
        | v664(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_94,axiom,
    ! [VarCurr: state_type] :
      ( v664(VarCurr)
    <=> ( v666(VarCurr)
        & v619(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_36,axiom,
    ! [VarCurr: state_type] :
      ( v666(VarCurr)
    <=> ( v667(VarCurr)
        & v487(VarCurr,5) ) ) ).

tff(writeBinaryOperatorShiftedRanges_35,axiom,
    ! [VarCurr: state_type] :
      ( v667(VarCurr)
    <=> ( v616(VarCurr)
        & v487(VarCurr,4) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_93,axiom,
    ! [VarCurr: state_type] :
      ( v655(VarCurr)
    <=> ( v656(VarCurr)
        | v661(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_34,axiom,
    ! [VarCurr: state_type] :
      ( v661(VarCurr)
    <=> ( v663(VarCurr)
        & v487(VarCurr,6) ) ) ).

tff(writeBinaryOperatorShiftedRanges_33,axiom,
    ! [VarCurr: state_type] :
      ( v663(VarCurr)
    <=> ( v659(VarCurr)
        & v487(VarCurr,5) ) ) ).

tff(writeBinaryOperatorShiftedRanges_32,axiom,
    ! [VarCurr: state_type] :
      ( v656(VarCurr)
    <=> ( v658(VarCurr)
        & v487(VarCurr,6) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_92,axiom,
    ! [VarCurr: state_type] :
      ( v658(VarCurr)
    <=> ( v659(VarCurr)
        & v618(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_31,axiom,
    ! [VarCurr: state_type] :
      ( v659(VarCurr)
    <=> ( v660(VarCurr)
        & v487(VarCurr,4) ) ) ).

tff(writeBinaryOperatorShiftedRanges_30,axiom,
    ! [VarCurr: state_type] :
      ( v660(VarCurr)
    <=> ( v611(VarCurr)
        & v487(VarCurr,3) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_91,axiom,
    ! [VarCurr: state_type] :
      ( v645(VarCurr)
    <=> ( v646(VarCurr)
        | v648(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_90,axiom,
    ! [VarCurr: state_type] :
      ( v648(VarCurr)
    <=> ( v650(VarCurr)
        & v619(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_89,axiom,
    ! [VarCurr: state_type] :
      ( v650(VarCurr)
    <=> ( v651(VarCurr)
        & v618(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_88,axiom,
    ! [VarCurr: state_type] :
      ( v651(VarCurr)
    <=> ( v652(VarCurr)
        & v617(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_29,axiom,
    ! [VarCurr: state_type] :
      ( v652(VarCurr)
    <=> ( v628(VarCurr)
        & v487(VarCurr,3) ) ) ).

tff(writeBinaryOperatorShiftedRanges_28,axiom,
    ! [VarCurr: state_type] :
      ( v646(VarCurr)
    <=> ( v639(VarCurr)
        & v487(VarCurr,6) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_17,axiom,
    ! [VarCurr: state_type] :
      ( ~ v584(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,2)
            & ~ $less(B,0) )
         => ( v644(VarCurr,B)
          <=> $false ) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_17,axiom,
    ! [VarCurr: state_type] :
      ( v584(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,2)
            & ~ $less(B,0) )
         => ( v644(VarCurr,B)
          <=> b10(B) ) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_87,axiom,
    ! [VarCurr: state_type] :
      ( v637(VarCurr)
    <=> ( v639(VarCurr)
        & v619(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_86,axiom,
    ! [VarCurr: state_type] :
      ( v639(VarCurr)
    <=> ( v640(VarCurr)
        & v618(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_85,axiom,
    ! [VarCurr: state_type] :
      ( v640(VarCurr)
    <=> ( v641(VarCurr)
        & v617(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_27,axiom,
    ! [VarCurr: state_type] :
      ( v641(VarCurr)
    <=> ( v642(VarCurr)
        & v487(VarCurr,3) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_84,axiom,
    ! [VarCurr: state_type] :
      ( v642(VarCurr)
    <=> ( v643(VarCurr)
        & v615(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_26,axiom,
    ! [VarCurr: state_type] :
      ( v643(VarCurr)
    <=> ( v613(VarCurr)
        & v487(VarCurr,1) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_83,axiom,
    ! [VarCurr: state_type] :
      ( v600(VarCurr)
    <=> ( v602(VarCurr)
        | v635(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_25,axiom,
    ! [VarCurr: state_type] :
      ( v635(VarCurr)
    <=> ( v622(VarCurr)
        & v487(VarCurr,6) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_82,axiom,
    ! [VarCurr: state_type] :
      ( v602(VarCurr)
    <=> ( v603(VarCurr)
        | v633(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_24,axiom,
    ! [VarCurr: state_type] :
      ( v633(VarCurr)
    <=> ( v608(VarCurr)
        & v487(VarCurr,6) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_81,axiom,
    ! [VarCurr: state_type] :
      ( v603(VarCurr)
    <=> ( v604(VarCurr)
        | v630(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_80,axiom,
    ! [VarCurr: state_type] :
      ( v630(VarCurr)
    <=> ( v632(VarCurr)
        & v619(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_23,axiom,
    ! [VarCurr: state_type] :
      ( v632(VarCurr)
    <=> ( v626(VarCurr)
        & v487(VarCurr,5) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_79,axiom,
    ! [VarCurr: state_type] :
      ( v604(VarCurr)
    <=> ( v605(VarCurr)
        | v623(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_78,axiom,
    ! [VarCurr: state_type] :
      ( v623(VarCurr)
    <=> ( v625(VarCurr)
        & v619(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_77,axiom,
    ! [VarCurr: state_type] :
      ( v625(VarCurr)
    <=> ( v626(VarCurr)
        & v618(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_76,axiom,
    ! [VarCurr: state_type] :
      ( v626(VarCurr)
    <=> ( v627(VarCurr)
        & v617(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_75,axiom,
    ! [VarCurr: state_type] :
      ( v627(VarCurr)
    <=> ( v628(VarCurr)
        & v616(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_74,axiom,
    ! [VarCurr: state_type] :
      ( v628(VarCurr)
    <=> ( v629(VarCurr)
        & v615(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_73,axiom,
    ! [VarCurr: state_type] :
      ( v629(VarCurr)
    <=> ( v487(VarCurr,0)
        & v614(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_72,axiom,
    ! [VarCurr: state_type] :
      ( v605(VarCurr)
    <=> ( v606(VarCurr)
        | v620(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_71,axiom,
    ! [VarCurr: state_type] :
      ( v620(VarCurr)
    <=> ( v622(VarCurr)
        & v619(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_22,axiom,
    ! [VarCurr: state_type] :
      ( v622(VarCurr)
    <=> ( v609(VarCurr)
        & v487(VarCurr,5) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_70,axiom,
    ! [VarCurr: state_type] :
      ( v606(VarCurr)
    <=> ( v608(VarCurr)
        & v619(VarCurr) ) ) ).

tff(writeUnaryOperator_48,axiom,
    ! [VarCurr: state_type] :
      ( ~ v619(VarCurr)
    <=> v487(VarCurr,6) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_69,axiom,
    ! [VarCurr: state_type] :
      ( v608(VarCurr)
    <=> ( v609(VarCurr)
        & v618(VarCurr) ) ) ).

tff(writeUnaryOperator_47,axiom,
    ! [VarCurr: state_type] :
      ( ~ v618(VarCurr)
    <=> v487(VarCurr,5) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_68,axiom,
    ! [VarCurr: state_type] :
      ( v609(VarCurr)
    <=> ( v610(VarCurr)
        & v617(VarCurr) ) ) ).

tff(writeUnaryOperator_46,axiom,
    ! [VarCurr: state_type] :
      ( ~ v617(VarCurr)
    <=> v487(VarCurr,4) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_67,axiom,
    ! [VarCurr: state_type] :
      ( v610(VarCurr)
    <=> ( v611(VarCurr)
        & v616(VarCurr) ) ) ).

tff(writeUnaryOperator_45,axiom,
    ! [VarCurr: state_type] :
      ( ~ v616(VarCurr)
    <=> v487(VarCurr,3) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_66,axiom,
    ! [VarCurr: state_type] :
      ( v611(VarCurr)
    <=> ( v612(VarCurr)
        & v615(VarCurr) ) ) ).

tff(writeUnaryOperator_44,axiom,
    ! [VarCurr: state_type] :
      ( ~ v615(VarCurr)
    <=> v487(VarCurr,2) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_65,axiom,
    ! [VarCurr: state_type] :
      ( v612(VarCurr)
    <=> ( v613(VarCurr)
        & v614(VarCurr) ) ) ).

tff(writeUnaryOperator_43,axiom,
    ! [VarCurr: state_type] :
      ( ~ v614(VarCurr)
    <=> v487(VarCurr,1) ) ).

tff(writeUnaryOperator_42,axiom,
    ! [VarCurr: state_type] :
      ( ~ v613(VarCurr)
    <=> v487(VarCurr,0) ) ).

tff(addAssignment_174,axiom,
    ! [VarCurr: state_type] :
      ( v584(VarCurr)
    <=> v489(VarCurr,81) ) ).

tff(addAssignment_173,axiom,
    ! [VarCurr: state_type] :
      ( v489(VarCurr,81)
    <=> v491(VarCurr,81) ) ).

tff(addAssignment_172,axiom,
    ! [VarCurr: state_type] :
      ( v491(VarCurr,81)
    <=> v493(VarCurr,696) ) ).

tff(addAssignment_171,axiom,
    ! [VarNext: state_type] :
      ( v493(VarNext,696)
    <=> v586(VarNext,81) ) ).

tff(addCaseBooleanConditionShiftedRanges1_1,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v588(VarNext)
       => ( ( v586(VarNext,122)
          <=> v493(VarCurr,737) )
          & ( v586(VarNext,121)
          <=> v493(VarCurr,736) )
          & ( v586(VarNext,120)
          <=> v493(VarCurr,735) )
          & ( v586(VarNext,119)
          <=> v493(VarCurr,734) )
          & ( v586(VarNext,118)
          <=> v493(VarCurr,733) )
          & ( v586(VarNext,117)
          <=> v493(VarCurr,732) )
          & ( v586(VarNext,116)
          <=> v493(VarCurr,731) )
          & ( v586(VarNext,115)
          <=> v493(VarCurr,730) )
          & ( v586(VarNext,114)
          <=> v493(VarCurr,729) )
          & ( v586(VarNext,113)
          <=> v493(VarCurr,728) )
          & ( v586(VarNext,112)
          <=> v493(VarCurr,727) )
          & ( v586(VarNext,111)
          <=> v493(VarCurr,726) )
          & ( v586(VarNext,110)
          <=> v493(VarCurr,725) )
          & ( v586(VarNext,109)
          <=> v493(VarCurr,724) )
          & ( v586(VarNext,108)
          <=> v493(VarCurr,723) )
          & ( v586(VarNext,107)
          <=> v493(VarCurr,722) )
          & ( v586(VarNext,106)
          <=> v493(VarCurr,721) )
          & ( v586(VarNext,105)
          <=> v493(VarCurr,720) )
          & ( v586(VarNext,104)
          <=> v493(VarCurr,719) )
          & ( v586(VarNext,103)
          <=> v493(VarCurr,718) )
          & ( v586(VarNext,102)
          <=> v493(VarCurr,717) )
          & ( v586(VarNext,101)
          <=> v493(VarCurr,716) )
          & ( v586(VarNext,100)
          <=> v493(VarCurr,715) )
          & ( v586(VarNext,99)
          <=> v493(VarCurr,714) )
          & ( v586(VarNext,98)
          <=> v493(VarCurr,713) )
          & ( v586(VarNext,97)
          <=> v493(VarCurr,712) )
          & ( v586(VarNext,96)
          <=> v493(VarCurr,711) )
          & ( v586(VarNext,95)
          <=> v493(VarCurr,710) )
          & ( v586(VarNext,94)
          <=> v493(VarCurr,709) )
          & ( v586(VarNext,93)
          <=> v493(VarCurr,708) )
          & ( v586(VarNext,92)
          <=> v493(VarCurr,707) )
          & ( v586(VarNext,91)
          <=> v493(VarCurr,706) )
          & ( v586(VarNext,90)
          <=> v493(VarCurr,705) )
          & ( v586(VarNext,89)
          <=> v493(VarCurr,704) )
          & ( v586(VarNext,88)
          <=> v493(VarCurr,703) )
          & ( v586(VarNext,87)
          <=> v493(VarCurr,702) )
          & ( v586(VarNext,86)
          <=> v493(VarCurr,701) )
          & ( v586(VarNext,85)
          <=> v493(VarCurr,700) )
          & ( v586(VarNext,84)
          <=> v493(VarCurr,699) )
          & ( v586(VarNext,83)
          <=> v493(VarCurr,698) )
          & ( v586(VarNext,82)
          <=> v493(VarCurr,697) )
          & ( v586(VarNext,81)
          <=> v493(VarCurr,696) )
          & ( v586(VarNext,80)
          <=> v493(VarCurr,695) )
          & ( v586(VarNext,79)
          <=> v493(VarCurr,694) )
          & ( v586(VarNext,78)
          <=> v493(VarCurr,693) )
          & ( v586(VarNext,77)
          <=> v493(VarCurr,692) )
          & ( v586(VarNext,76)
          <=> v493(VarCurr,691) )
          & ( v586(VarNext,75)
          <=> v493(VarCurr,690) )
          & ( v586(VarNext,74)
          <=> v493(VarCurr,689) )
          & ( v586(VarNext,73)
          <=> v493(VarCurr,688) )
          & ( v586(VarNext,72)
          <=> v493(VarCurr,687) )
          & ( v586(VarNext,71)
          <=> v493(VarCurr,686) )
          & ( v586(VarNext,70)
          <=> v493(VarCurr,685) )
          & ( v586(VarNext,69)
          <=> v493(VarCurr,684) )
          & ( v586(VarNext,68)
          <=> v493(VarCurr,683) )
          & ( v586(VarNext,67)
          <=> v493(VarCurr,682) )
          & ( v586(VarNext,66)
          <=> v493(VarCurr,681) )
          & ( v586(VarNext,65)
          <=> v493(VarCurr,680) )
          & ( v586(VarNext,64)
          <=> v493(VarCurr,679) )
          & ( v586(VarNext,63)
          <=> v493(VarCurr,678) )
          & ( v586(VarNext,62)
          <=> v493(VarCurr,677) )
          & ( v586(VarNext,61)
          <=> v493(VarCurr,676) )
          & ( v586(VarNext,60)
          <=> v493(VarCurr,675) )
          & ( v586(VarNext,59)
          <=> v493(VarCurr,674) )
          & ( v586(VarNext,58)
          <=> v493(VarCurr,673) )
          & ( v586(VarNext,57)
          <=> v493(VarCurr,672) )
          & ( v586(VarNext,56)
          <=> v493(VarCurr,671) )
          & ( v586(VarNext,55)
          <=> v493(VarCurr,670) )
          & ( v586(VarNext,54)
          <=> v493(VarCurr,669) )
          & ( v586(VarNext,53)
          <=> v493(VarCurr,668) )
          & ( v586(VarNext,52)
          <=> v493(VarCurr,667) )
          & ( v586(VarNext,51)
          <=> v493(VarCurr,666) )
          & ( v586(VarNext,50)
          <=> v493(VarCurr,665) )
          & ( v586(VarNext,49)
          <=> v493(VarCurr,664) )
          & ( v586(VarNext,48)
          <=> v493(VarCurr,663) )
          & ( v586(VarNext,47)
          <=> v493(VarCurr,662) )
          & ( v586(VarNext,46)
          <=> v493(VarCurr,661) )
          & ( v586(VarNext,45)
          <=> v493(VarCurr,660) )
          & ( v586(VarNext,44)
          <=> v493(VarCurr,659) )
          & ( v586(VarNext,43)
          <=> v493(VarCurr,658) )
          & ( v586(VarNext,42)
          <=> v493(VarCurr,657) )
          & ( v586(VarNext,41)
          <=> v493(VarCurr,656) )
          & ( v586(VarNext,40)
          <=> v493(VarCurr,655) )
          & ( v586(VarNext,39)
          <=> v493(VarCurr,654) )
          & ( v586(VarNext,38)
          <=> v493(VarCurr,653) )
          & ( v586(VarNext,37)
          <=> v493(VarCurr,652) )
          & ( v586(VarNext,36)
          <=> v493(VarCurr,651) )
          & ( v586(VarNext,35)
          <=> v493(VarCurr,650) )
          & ( v586(VarNext,34)
          <=> v493(VarCurr,649) )
          & ( v586(VarNext,33)
          <=> v493(VarCurr,648) )
          & ( v586(VarNext,32)
          <=> v493(VarCurr,647) )
          & ( v586(VarNext,31)
          <=> v493(VarCurr,646) )
          & ( v586(VarNext,30)
          <=> v493(VarCurr,645) )
          & ( v586(VarNext,29)
          <=> v493(VarCurr,644) )
          & ( v586(VarNext,28)
          <=> v493(VarCurr,643) )
          & ( v586(VarNext,27)
          <=> v493(VarCurr,642) )
          & ( v586(VarNext,26)
          <=> v493(VarCurr,641) )
          & ( v586(VarNext,25)
          <=> v493(VarCurr,640) )
          & ( v586(VarNext,24)
          <=> v493(VarCurr,639) )
          & ( v586(VarNext,23)
          <=> v493(VarCurr,638) )
          & ( v586(VarNext,22)
          <=> v493(VarCurr,637) )
          & ( v586(VarNext,21)
          <=> v493(VarCurr,636) )
          & ( v586(VarNext,20)
          <=> v493(VarCurr,635) )
          & ( v586(VarNext,19)
          <=> v493(VarCurr,634) )
          & ( v586(VarNext,18)
          <=> v493(VarCurr,633) )
          & ( v586(VarNext,17)
          <=> v493(VarCurr,632) )
          & ( v586(VarNext,16)
          <=> v493(VarCurr,631) )
          & ( v586(VarNext,15)
          <=> v493(VarCurr,630) )
          & ( v586(VarNext,14)
          <=> v493(VarCurr,629) )
          & ( v586(VarNext,13)
          <=> v493(VarCurr,628) )
          & ( v586(VarNext,12)
          <=> v493(VarCurr,627) )
          & ( v586(VarNext,11)
          <=> v493(VarCurr,626) )
          & ( v586(VarNext,10)
          <=> v493(VarCurr,625) )
          & ( v586(VarNext,9)
          <=> v493(VarCurr,624) )
          & ( v586(VarNext,8)
          <=> v493(VarCurr,623) )
          & ( v586(VarNext,7)
          <=> v493(VarCurr,622) )
          & ( v586(VarNext,6)
          <=> v493(VarCurr,621) )
          & ( v586(VarNext,5)
          <=> v493(VarCurr,620) )
          & ( v586(VarNext,4)
          <=> v493(VarCurr,619) )
          & ( v586(VarNext,3)
          <=> v493(VarCurr,618) )
          & ( v586(VarNext,2)
          <=> v493(VarCurr,617) )
          & ( v586(VarNext,1)
          <=> v493(VarCurr,616) )
          & ( v586(VarNext,0)
          <=> v493(VarCurr,615) ) ) ) ) ).

tff(addCaseBooleanConditionEqualRanges0_4,axiom,
    ! [VarNext: state_type] :
      ( v588(VarNext)
     => ! [B: $int] :
          ( ( $less(B,123)
            & ~ $less(B,0) )
         => ( v586(VarNext,B)
          <=> v573(VarNext,B) ) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_64,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v588(VarNext)
      <=> ( v589(VarNext)
          & v554(VarNext) ) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_63,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v589(VarNext)
      <=> ( v591(VarNext)
          & v459(VarNext) ) ) ) ).

tff(writeUnaryOperator_41,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v591(VarNext)
      <=> v466(VarNext) ) ) ).

tff(addAssignment_170,axiom,
    ! [VarCurr: state_type] :
      ( v538(VarCurr,81)
    <=> v543(VarCurr,81) ) ).

tff(addAssignment_169,axiom,
    ! [VarCurr: state_type] :
      ( v542(VarCurr,81)
    <=> v493(VarCurr,573) ) ).

tff(addAssignment_168,axiom,
    ! [VarCurr: state_type] :
      ( v496(VarCurr,81)
    <=> v536(VarCurr,81) ) ).

tff(addAssignment_167,axiom,
    ! [VarCurr: state_type] :
      ( v535(VarCurr,81)
    <=> v493(VarCurr,696) ) ).

tff(addAssignment_166,axiom,
    ! [VarCurr: state_type] :
      ( v519(VarCurr,81)
    <=> v521(VarCurr,81) ) ).

tff(addAssignment_165,axiom,
    ! [VarCurr: state_type] :
      ( v521(VarCurr,81)
    <=> v523(VarCurr,81) ) ).

tff(addAssignment_164,axiom,
    ! [VarCurr: state_type] :
      ( v523(VarCurr,81)
    <=> v525(VarCurr,81) ) ).

tff(addAssignment_163,axiom,
    ! [VarCurr: state_type] :
      ( v525(VarCurr,81)
    <=> v527(VarCurr,81) ) ).

tff(addAssignment_162,axiom,
    ! [VarCurr: state_type] :
      ( v527(VarCurr,81)
    <=> v529(VarCurr,81) ) ).

tff(addAssignment_161,axiom,
    ! [VarCurr: state_type] :
      ( v529(VarCurr,81)
    <=> v531(VarCurr,81) ) ).

tff(addAssignment_160,axiom,
    ! [VarCurr: state_type] :
      ( v531(VarCurr,81)
    <=> v533(VarCurr,81) ) ).

tff(addAssignment_159,axiom,
    ! [VarCurr: state_type] :
      ( ( v487(VarCurr,6)
      <=> v489(VarCurr,122) )
      & ( v487(VarCurr,5)
      <=> v489(VarCurr,121) )
      & ( v487(VarCurr,4)
      <=> v489(VarCurr,120) )
      & ( v487(VarCurr,3)
      <=> v489(VarCurr,119) )
      & ( v487(VarCurr,2)
      <=> v489(VarCurr,118) )
      & ( v487(VarCurr,1)
      <=> v489(VarCurr,117) )
      & ( v487(VarCurr,0)
      <=> v489(VarCurr,116) ) ) ).

tff(addAssignment_158,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,123)
        & ~ $less(B,116) )
     => ( v489(VarCurr,B)
      <=> v491(VarCurr,B) ) ) ).

tff(addAssignment_157,axiom,
    ! [VarCurr: state_type] :
      ( ( v491(VarCurr,122)
      <=> v493(VarCurr,737) )
      & ( v491(VarCurr,121)
      <=> v493(VarCurr,736) )
      & ( v491(VarCurr,120)
      <=> v493(VarCurr,735) )
      & ( v491(VarCurr,119)
      <=> v493(VarCurr,734) )
      & ( v491(VarCurr,118)
      <=> v493(VarCurr,733) )
      & ( v491(VarCurr,117)
      <=> v493(VarCurr,732) )
      & ( v491(VarCurr,116)
      <=> v493(VarCurr,731) ) ) ).

tff(addAssignment_156,axiom,
    ! [VarNext: state_type] :
      ( ( v493(VarNext,737)
      <=> v545(VarNext,122) )
      & ( v493(VarNext,736)
      <=> v545(VarNext,121) )
      & ( v493(VarNext,735)
      <=> v545(VarNext,120) )
      & ( v493(VarNext,734)
      <=> v545(VarNext,119) )
      & ( v493(VarNext,733)
      <=> v545(VarNext,118) )
      & ( v493(VarNext,732)
      <=> v545(VarNext,117) )
      & ( v493(VarNext,731)
      <=> v545(VarNext,116) ) ) ).

tff(addCaseBooleanConditionShiftedRanges1,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v546(VarNext)
       => ( ( v545(VarNext,122)
          <=> v493(VarCurr,737) )
          & ( v545(VarNext,121)
          <=> v493(VarCurr,736) )
          & ( v545(VarNext,120)
          <=> v493(VarCurr,735) )
          & ( v545(VarNext,119)
          <=> v493(VarCurr,734) )
          & ( v545(VarNext,118)
          <=> v493(VarCurr,733) )
          & ( v545(VarNext,117)
          <=> v493(VarCurr,732) )
          & ( v545(VarNext,116)
          <=> v493(VarCurr,731) )
          & ( v545(VarNext,115)
          <=> v493(VarCurr,730) )
          & ( v545(VarNext,114)
          <=> v493(VarCurr,729) )
          & ( v545(VarNext,113)
          <=> v493(VarCurr,728) )
          & ( v545(VarNext,112)
          <=> v493(VarCurr,727) )
          & ( v545(VarNext,111)
          <=> v493(VarCurr,726) )
          & ( v545(VarNext,110)
          <=> v493(VarCurr,725) )
          & ( v545(VarNext,109)
          <=> v493(VarCurr,724) )
          & ( v545(VarNext,108)
          <=> v493(VarCurr,723) )
          & ( v545(VarNext,107)
          <=> v493(VarCurr,722) )
          & ( v545(VarNext,106)
          <=> v493(VarCurr,721) )
          & ( v545(VarNext,105)
          <=> v493(VarCurr,720) )
          & ( v545(VarNext,104)
          <=> v493(VarCurr,719) )
          & ( v545(VarNext,103)
          <=> v493(VarCurr,718) )
          & ( v545(VarNext,102)
          <=> v493(VarCurr,717) )
          & ( v545(VarNext,101)
          <=> v493(VarCurr,716) )
          & ( v545(VarNext,100)
          <=> v493(VarCurr,715) )
          & ( v545(VarNext,99)
          <=> v493(VarCurr,714) )
          & ( v545(VarNext,98)
          <=> v493(VarCurr,713) )
          & ( v545(VarNext,97)
          <=> v493(VarCurr,712) )
          & ( v545(VarNext,96)
          <=> v493(VarCurr,711) )
          & ( v545(VarNext,95)
          <=> v493(VarCurr,710) )
          & ( v545(VarNext,94)
          <=> v493(VarCurr,709) )
          & ( v545(VarNext,93)
          <=> v493(VarCurr,708) )
          & ( v545(VarNext,92)
          <=> v493(VarCurr,707) )
          & ( v545(VarNext,91)
          <=> v493(VarCurr,706) )
          & ( v545(VarNext,90)
          <=> v493(VarCurr,705) )
          & ( v545(VarNext,89)
          <=> v493(VarCurr,704) )
          & ( v545(VarNext,88)
          <=> v493(VarCurr,703) )
          & ( v545(VarNext,87)
          <=> v493(VarCurr,702) )
          & ( v545(VarNext,86)
          <=> v493(VarCurr,701) )
          & ( v545(VarNext,85)
          <=> v493(VarCurr,700) )
          & ( v545(VarNext,84)
          <=> v493(VarCurr,699) )
          & ( v545(VarNext,83)
          <=> v493(VarCurr,698) )
          & ( v545(VarNext,82)
          <=> v493(VarCurr,697) )
          & ( v545(VarNext,81)
          <=> v493(VarCurr,696) )
          & ( v545(VarNext,80)
          <=> v493(VarCurr,695) )
          & ( v545(VarNext,79)
          <=> v493(VarCurr,694) )
          & ( v545(VarNext,78)
          <=> v493(VarCurr,693) )
          & ( v545(VarNext,77)
          <=> v493(VarCurr,692) )
          & ( v545(VarNext,76)
          <=> v493(VarCurr,691) )
          & ( v545(VarNext,75)
          <=> v493(VarCurr,690) )
          & ( v545(VarNext,74)
          <=> v493(VarCurr,689) )
          & ( v545(VarNext,73)
          <=> v493(VarCurr,688) )
          & ( v545(VarNext,72)
          <=> v493(VarCurr,687) )
          & ( v545(VarNext,71)
          <=> v493(VarCurr,686) )
          & ( v545(VarNext,70)
          <=> v493(VarCurr,685) )
          & ( v545(VarNext,69)
          <=> v493(VarCurr,684) )
          & ( v545(VarNext,68)
          <=> v493(VarCurr,683) )
          & ( v545(VarNext,67)
          <=> v493(VarCurr,682) )
          & ( v545(VarNext,66)
          <=> v493(VarCurr,681) )
          & ( v545(VarNext,65)
          <=> v493(VarCurr,680) )
          & ( v545(VarNext,64)
          <=> v493(VarCurr,679) )
          & ( v545(VarNext,63)
          <=> v493(VarCurr,678) )
          & ( v545(VarNext,62)
          <=> v493(VarCurr,677) )
          & ( v545(VarNext,61)
          <=> v493(VarCurr,676) )
          & ( v545(VarNext,60)
          <=> v493(VarCurr,675) )
          & ( v545(VarNext,59)
          <=> v493(VarCurr,674) )
          & ( v545(VarNext,58)
          <=> v493(VarCurr,673) )
          & ( v545(VarNext,57)
          <=> v493(VarCurr,672) )
          & ( v545(VarNext,56)
          <=> v493(VarCurr,671) )
          & ( v545(VarNext,55)
          <=> v493(VarCurr,670) )
          & ( v545(VarNext,54)
          <=> v493(VarCurr,669) )
          & ( v545(VarNext,53)
          <=> v493(VarCurr,668) )
          & ( v545(VarNext,52)
          <=> v493(VarCurr,667) )
          & ( v545(VarNext,51)
          <=> v493(VarCurr,666) )
          & ( v545(VarNext,50)
          <=> v493(VarCurr,665) )
          & ( v545(VarNext,49)
          <=> v493(VarCurr,664) )
          & ( v545(VarNext,48)
          <=> v493(VarCurr,663) )
          & ( v545(VarNext,47)
          <=> v493(VarCurr,662) )
          & ( v545(VarNext,46)
          <=> v493(VarCurr,661) )
          & ( v545(VarNext,45)
          <=> v493(VarCurr,660) )
          & ( v545(VarNext,44)
          <=> v493(VarCurr,659) )
          & ( v545(VarNext,43)
          <=> v493(VarCurr,658) )
          & ( v545(VarNext,42)
          <=> v493(VarCurr,657) )
          & ( v545(VarNext,41)
          <=> v493(VarCurr,656) )
          & ( v545(VarNext,40)
          <=> v493(VarCurr,655) )
          & ( v545(VarNext,39)
          <=> v493(VarCurr,654) )
          & ( v545(VarNext,38)
          <=> v493(VarCurr,653) )
          & ( v545(VarNext,37)
          <=> v493(VarCurr,652) )
          & ( v545(VarNext,36)
          <=> v493(VarCurr,651) )
          & ( v545(VarNext,35)
          <=> v493(VarCurr,650) )
          & ( v545(VarNext,34)
          <=> v493(VarCurr,649) )
          & ( v545(VarNext,33)
          <=> v493(VarCurr,648) )
          & ( v545(VarNext,32)
          <=> v493(VarCurr,647) )
          & ( v545(VarNext,31)
          <=> v493(VarCurr,646) )
          & ( v545(VarNext,30)
          <=> v493(VarCurr,645) )
          & ( v545(VarNext,29)
          <=> v493(VarCurr,644) )
          & ( v545(VarNext,28)
          <=> v493(VarCurr,643) )
          & ( v545(VarNext,27)
          <=> v493(VarCurr,642) )
          & ( v545(VarNext,26)
          <=> v493(VarCurr,641) )
          & ( v545(VarNext,25)
          <=> v493(VarCurr,640) )
          & ( v545(VarNext,24)
          <=> v493(VarCurr,639) )
          & ( v545(VarNext,23)
          <=> v493(VarCurr,638) )
          & ( v545(VarNext,22)
          <=> v493(VarCurr,637) )
          & ( v545(VarNext,21)
          <=> v493(VarCurr,636) )
          & ( v545(VarNext,20)
          <=> v493(VarCurr,635) )
          & ( v545(VarNext,19)
          <=> v493(VarCurr,634) )
          & ( v545(VarNext,18)
          <=> v493(VarCurr,633) )
          & ( v545(VarNext,17)
          <=> v493(VarCurr,632) )
          & ( v545(VarNext,16)
          <=> v493(VarCurr,631) )
          & ( v545(VarNext,15)
          <=> v493(VarCurr,630) )
          & ( v545(VarNext,14)
          <=> v493(VarCurr,629) )
          & ( v545(VarNext,13)
          <=> v493(VarCurr,628) )
          & ( v545(VarNext,12)
          <=> v493(VarCurr,627) )
          & ( v545(VarNext,11)
          <=> v493(VarCurr,626) )
          & ( v545(VarNext,10)
          <=> v493(VarCurr,625) )
          & ( v545(VarNext,9)
          <=> v493(VarCurr,624) )
          & ( v545(VarNext,8)
          <=> v493(VarCurr,623) )
          & ( v545(VarNext,7)
          <=> v493(VarCurr,622) )
          & ( v545(VarNext,6)
          <=> v493(VarCurr,621) )
          & ( v545(VarNext,5)
          <=> v493(VarCurr,620) )
          & ( v545(VarNext,4)
          <=> v493(VarCurr,619) )
          & ( v545(VarNext,3)
          <=> v493(VarCurr,618) )
          & ( v545(VarNext,2)
          <=> v493(VarCurr,617) )
          & ( v545(VarNext,1)
          <=> v493(VarCurr,616) )
          & ( v545(VarNext,0)
          <=> v493(VarCurr,615) ) ) ) ) ).

tff(addCaseBooleanConditionEqualRanges0_3,axiom,
    ! [VarNext: state_type] :
      ( v546(VarNext)
     => ! [B: $int] :
          ( ( $less(B,123)
            & ~ $less(B,0) )
         => ( v545(VarNext,B)
          <=> v573(VarNext,B) ) ) ) ).

tff(addAssignment_155,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ! [B: $int] :
          ( ( $less(B,123)
            & ~ $less(B,0) )
         => ( v573(VarNext,B)
          <=> v571(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_9,axiom,
    ! [VarCurr: state_type] :
      ( ~ v556(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,123)
            & ~ $less(B,0) )
         => ( v571(VarCurr,B)
          <=> v574(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_8,axiom,
    ! [VarCurr: state_type] :
      ( v556(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,123)
            & ~ $less(B,0) )
         => ( v571(VarCurr,B)
          <=> $false ) ) ) ).

tff(bitBlastConstant_182,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(122) ).

tff(bitBlastConstant_181,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(121) ).

tff(bitBlastConstant_180,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(120) ).

tff(bitBlastConstant_179,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(119) ).

tff(bitBlastConstant_178,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(118) ).

tff(bitBlastConstant_177,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(117) ).

tff(bitBlastConstant_176,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(116) ).

tff(bitBlastConstant_175,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(115) ).

tff(bitBlastConstant_174,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(114) ).

tff(bitBlastConstant_173,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(113) ).

tff(bitBlastConstant_172,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(112) ).

tff(bitBlastConstant_171,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(111) ).

tff(bitBlastConstant_170,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(110) ).

tff(bitBlastConstant_169,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(109) ).

tff(bitBlastConstant_168,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(108) ).

tff(bitBlastConstant_167,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(107) ).

tff(bitBlastConstant_166,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(106) ).

tff(bitBlastConstant_165,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(105) ).

tff(bitBlastConstant_164,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(104) ).

tff(bitBlastConstant_163,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(103) ).

tff(bitBlastConstant_162,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(102) ).

tff(bitBlastConstant_161,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(101) ).

tff(bitBlastConstant_160,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(100) ).

tff(bitBlastConstant_159,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(99) ).

tff(bitBlastConstant_158,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(98) ).

tff(bitBlastConstant_157,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(97) ).

tff(bitBlastConstant_156,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(96) ).

tff(bitBlastConstant_155,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(95) ).

tff(bitBlastConstant_154,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(94) ).

tff(bitBlastConstant_153,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(93) ).

tff(bitBlastConstant_152,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(92) ).

tff(bitBlastConstant_151,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(91) ).

tff(bitBlastConstant_150,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(90) ).

tff(bitBlastConstant_149,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(89) ).

tff(bitBlastConstant_148,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(88) ).

tff(bitBlastConstant_147,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(87) ).

tff(bitBlastConstant_146,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(86) ).

tff(bitBlastConstant_145,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(85) ).

tff(bitBlastConstant_144,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(84) ).

tff(bitBlastConstant_143,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(83) ).

tff(bitBlastConstant_142,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(82) ).

tff(bitBlastConstant_141,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(81) ).

tff(bitBlastConstant_140,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(80) ).

tff(bitBlastConstant_139,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(79) ).

tff(bitBlastConstant_138,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(78) ).

tff(bitBlastConstant_137,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(77) ).

tff(bitBlastConstant_136,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(76) ).

tff(bitBlastConstant_135,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(75) ).

tff(bitBlastConstant_134,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(74) ).

tff(bitBlastConstant_133,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(73) ).

tff(bitBlastConstant_132,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(72) ).

tff(bitBlastConstant_131,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(71) ).

tff(bitBlastConstant_130,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(70) ).

tff(bitBlastConstant_129,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(69) ).

tff(bitBlastConstant_128,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(68) ).

tff(bitBlastConstant_127,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(67) ).

tff(bitBlastConstant_126,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(66) ).

tff(bitBlastConstant_125,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(65) ).

tff(bitBlastConstant_124,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(64) ).

tff(bitBlastConstant_123,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(63) ).

tff(bitBlastConstant_122,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(62) ).

tff(bitBlastConstant_121,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(61) ).

tff(bitBlastConstant_120,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(60) ).

tff(bitBlastConstant_119,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(59) ).

tff(bitBlastConstant_118,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(58) ).

tff(bitBlastConstant_117,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(57) ).

tff(bitBlastConstant_116,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(56) ).

tff(bitBlastConstant_115,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(55) ).

tff(bitBlastConstant_114,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(54) ).

tff(bitBlastConstant_113,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(53) ).

tff(bitBlastConstant_112,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(52) ).

tff(bitBlastConstant_111,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(51) ).

tff(bitBlastConstant_110,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(50) ).

tff(bitBlastConstant_109,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(49) ).

tff(bitBlastConstant_108,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(48) ).

tff(bitBlastConstant_107,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(47) ).

tff(bitBlastConstant_106,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(46) ).

tff(bitBlastConstant_105,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(45) ).

tff(bitBlastConstant_104,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(44) ).

tff(bitBlastConstant_103,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(43) ).

tff(bitBlastConstant_102,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(42) ).

tff(bitBlastConstant_101,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(41) ).

tff(bitBlastConstant_100,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(40) ).

tff(bitBlastConstant_99,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(39) ).

tff(bitBlastConstant_98,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(38) ).

tff(bitBlastConstant_97,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(37) ).

tff(bitBlastConstant_96,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(36) ).

tff(bitBlastConstant_95,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(35) ).

tff(bitBlastConstant_94,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(34) ).

tff(bitBlastConstant_93,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(33) ).

tff(bitBlastConstant_92,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(32) ).

tff(bitBlastConstant_91,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(31) ).

tff(bitBlastConstant_90,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(30) ).

tff(bitBlastConstant_89,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(29) ).

tff(bitBlastConstant_88,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(28) ).

tff(bitBlastConstant_87,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(27) ).

tff(bitBlastConstant_86,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(26) ).

tff(bitBlastConstant_85,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(25) ).

tff(bitBlastConstant_84,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(24) ).

tff(bitBlastConstant_83,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(23) ).

tff(bitBlastConstant_82,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(22) ).

tff(bitBlastConstant_81,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(21) ).

tff(bitBlastConstant_80,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(20) ).

tff(bitBlastConstant_79,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(19) ).

tff(bitBlastConstant_78,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(18) ).

tff(bitBlastConstant_77,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(17) ).

tff(bitBlastConstant_76,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(16) ).

tff(bitBlastConstant_75,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(15) ).

tff(bitBlastConstant_74,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(14) ).

tff(bitBlastConstant_73,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(13) ).

tff(bitBlastConstant_72,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(12) ).

tff(bitBlastConstant_71,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(11) ).

tff(bitBlastConstant_70,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(10) ).

tff(bitBlastConstant_69,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(9) ).

tff(bitBlastConstant_68,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(8) ).

tff(bitBlastConstant_67,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(7) ).

tff(bitBlastConstant_66,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(6) ).

tff(bitBlastConstant_65,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(5) ).

tff(bitBlastConstant_64,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(4) ).

tff(bitBlastConstant_63,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(3) ).

tff(bitBlastConstant_62,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(2) ).

tff(bitBlastConstant_61,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(1) ).

tff(bitBlastConstant_60,axiom,
    ~ b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000(0) ).

tff(addParallelCaseBooleanConditionEqualRanges2_4,axiom,
    ! [VarCurr: state_type] :
      ( ( ~ v560(VarCurr)
        & ~ v562(VarCurr) )
     => ! [B: $int] :
          ( ( $less(B,123)
            & ~ $less(B,0) )
         => ( v574(VarCurr,B)
          <=> v538(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_8,axiom,
    ! [VarCurr: state_type] :
      ( v562(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,123)
            & ~ $less(B,0) )
         => ( v574(VarCurr,B)
          <=> v496(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionShiftedRanges0,axiom,
    ! [VarCurr: state_type] :
      ( v560(VarCurr)
     => ( ( v574(VarCurr,122)
        <=> v493(VarCurr,614) )
        & ( v574(VarCurr,121)
        <=> v493(VarCurr,613) )
        & ( v574(VarCurr,120)
        <=> v493(VarCurr,612) )
        & ( v574(VarCurr,119)
        <=> v493(VarCurr,611) )
        & ( v574(VarCurr,118)
        <=> v493(VarCurr,610) )
        & ( v574(VarCurr,117)
        <=> v493(VarCurr,609) )
        & ( v574(VarCurr,116)
        <=> v493(VarCurr,608) )
        & ( v574(VarCurr,115)
        <=> v493(VarCurr,607) )
        & ( v574(VarCurr,114)
        <=> v493(VarCurr,606) )
        & ( v574(VarCurr,113)
        <=> v493(VarCurr,605) )
        & ( v574(VarCurr,112)
        <=> v493(VarCurr,604) )
        & ( v574(VarCurr,111)
        <=> v493(VarCurr,603) )
        & ( v574(VarCurr,110)
        <=> v493(VarCurr,602) )
        & ( v574(VarCurr,109)
        <=> v493(VarCurr,601) )
        & ( v574(VarCurr,108)
        <=> v493(VarCurr,600) )
        & ( v574(VarCurr,107)
        <=> v493(VarCurr,599) )
        & ( v574(VarCurr,106)
        <=> v493(VarCurr,598) )
        & ( v574(VarCurr,105)
        <=> v493(VarCurr,597) )
        & ( v574(VarCurr,104)
        <=> v493(VarCurr,596) )
        & ( v574(VarCurr,103)
        <=> v493(VarCurr,595) )
        & ( v574(VarCurr,102)
        <=> v493(VarCurr,594) )
        & ( v574(VarCurr,101)
        <=> v493(VarCurr,593) )
        & ( v574(VarCurr,100)
        <=> v493(VarCurr,592) )
        & ( v574(VarCurr,99)
        <=> v493(VarCurr,591) )
        & ( v574(VarCurr,98)
        <=> v493(VarCurr,590) )
        & ( v574(VarCurr,97)
        <=> v493(VarCurr,589) )
        & ( v574(VarCurr,96)
        <=> v493(VarCurr,588) )
        & ( v574(VarCurr,95)
        <=> v493(VarCurr,587) )
        & ( v574(VarCurr,94)
        <=> v493(VarCurr,586) )
        & ( v574(VarCurr,93)
        <=> v493(VarCurr,585) )
        & ( v574(VarCurr,92)
        <=> v493(VarCurr,584) )
        & ( v574(VarCurr,91)
        <=> v493(VarCurr,583) )
        & ( v574(VarCurr,90)
        <=> v493(VarCurr,582) )
        & ( v574(VarCurr,89)
        <=> v493(VarCurr,581) )
        & ( v574(VarCurr,88)
        <=> v493(VarCurr,580) )
        & ( v574(VarCurr,87)
        <=> v493(VarCurr,579) )
        & ( v574(VarCurr,86)
        <=> v493(VarCurr,578) )
        & ( v574(VarCurr,85)
        <=> v493(VarCurr,577) )
        & ( v574(VarCurr,84)
        <=> v493(VarCurr,576) )
        & ( v574(VarCurr,83)
        <=> v493(VarCurr,575) )
        & ( v574(VarCurr,82)
        <=> v493(VarCurr,574) )
        & ( v574(VarCurr,81)
        <=> v493(VarCurr,573) )
        & ( v574(VarCurr,80)
        <=> v493(VarCurr,572) )
        & ( v574(VarCurr,79)
        <=> v493(VarCurr,571) )
        & ( v574(VarCurr,78)
        <=> v493(VarCurr,570) )
        & ( v574(VarCurr,77)
        <=> v493(VarCurr,569) )
        & ( v574(VarCurr,76)
        <=> v493(VarCurr,568) )
        & ( v574(VarCurr,75)
        <=> v493(VarCurr,567) )
        & ( v574(VarCurr,74)
        <=> v493(VarCurr,566) )
        & ( v574(VarCurr,73)
        <=> v493(VarCurr,565) )
        & ( v574(VarCurr,72)
        <=> v493(VarCurr,564) )
        & ( v574(VarCurr,71)
        <=> v493(VarCurr,563) )
        & ( v574(VarCurr,70)
        <=> v493(VarCurr,562) )
        & ( v574(VarCurr,69)
        <=> v493(VarCurr,561) )
        & ( v574(VarCurr,68)
        <=> v493(VarCurr,560) )
        & ( v574(VarCurr,67)
        <=> v493(VarCurr,559) )
        & ( v574(VarCurr,66)
        <=> v493(VarCurr,558) )
        & ( v574(VarCurr,65)
        <=> v493(VarCurr,557) )
        & ( v574(VarCurr,64)
        <=> v493(VarCurr,556) )
        & ( v574(VarCurr,63)
        <=> v493(VarCurr,555) )
        & ( v574(VarCurr,62)
        <=> v493(VarCurr,554) )
        & ( v574(VarCurr,61)
        <=> v493(VarCurr,553) )
        & ( v574(VarCurr,60)
        <=> v493(VarCurr,552) )
        & ( v574(VarCurr,59)
        <=> v493(VarCurr,551) )
        & ( v574(VarCurr,58)
        <=> v493(VarCurr,550) )
        & ( v574(VarCurr,57)
        <=> v493(VarCurr,549) )
        & ( v574(VarCurr,56)
        <=> v493(VarCurr,548) )
        & ( v574(VarCurr,55)
        <=> v493(VarCurr,547) )
        & ( v574(VarCurr,54)
        <=> v493(VarCurr,546) )
        & ( v574(VarCurr,53)
        <=> v493(VarCurr,545) )
        & ( v574(VarCurr,52)
        <=> v493(VarCurr,544) )
        & ( v574(VarCurr,51)
        <=> v493(VarCurr,543) )
        & ( v574(VarCurr,50)
        <=> v493(VarCurr,542) )
        & ( v574(VarCurr,49)
        <=> v493(VarCurr,541) )
        & ( v574(VarCurr,48)
        <=> v493(VarCurr,540) )
        & ( v574(VarCurr,47)
        <=> v493(VarCurr,539) )
        & ( v574(VarCurr,46)
        <=> v493(VarCurr,538) )
        & ( v574(VarCurr,45)
        <=> v493(VarCurr,537) )
        & ( v574(VarCurr,44)
        <=> v493(VarCurr,536) )
        & ( v574(VarCurr,43)
        <=> v493(VarCurr,535) )
        & ( v574(VarCurr,42)
        <=> v493(VarCurr,534) )
        & ( v574(VarCurr,41)
        <=> v493(VarCurr,533) )
        & ( v574(VarCurr,40)
        <=> v493(VarCurr,532) )
        & ( v574(VarCurr,39)
        <=> v493(VarCurr,531) )
        & ( v574(VarCurr,38)
        <=> v493(VarCurr,530) )
        & ( v574(VarCurr,37)
        <=> v493(VarCurr,529) )
        & ( v574(VarCurr,36)
        <=> v493(VarCurr,528) )
        & ( v574(VarCurr,35)
        <=> v493(VarCurr,527) )
        & ( v574(VarCurr,34)
        <=> v493(VarCurr,526) )
        & ( v574(VarCurr,33)
        <=> v493(VarCurr,525) )
        & ( v574(VarCurr,32)
        <=> v493(VarCurr,524) )
        & ( v574(VarCurr,31)
        <=> v493(VarCurr,523) )
        & ( v574(VarCurr,30)
        <=> v493(VarCurr,522) )
        & ( v574(VarCurr,29)
        <=> v493(VarCurr,521) )
        & ( v574(VarCurr,28)
        <=> v493(VarCurr,520) )
        & ( v574(VarCurr,27)
        <=> v493(VarCurr,519) )
        & ( v574(VarCurr,26)
        <=> v493(VarCurr,518) )
        & ( v574(VarCurr,25)
        <=> v493(VarCurr,517) )
        & ( v574(VarCurr,24)
        <=> v493(VarCurr,516) )
        & ( v574(VarCurr,23)
        <=> v493(VarCurr,515) )
        & ( v574(VarCurr,22)
        <=> v493(VarCurr,514) )
        & ( v574(VarCurr,21)
        <=> v493(VarCurr,513) )
        & ( v574(VarCurr,20)
        <=> v493(VarCurr,512) )
        & ( v574(VarCurr,19)
        <=> v493(VarCurr,511) )
        & ( v574(VarCurr,18)
        <=> v493(VarCurr,510) )
        & ( v574(VarCurr,17)
        <=> v493(VarCurr,509) )
        & ( v574(VarCurr,16)
        <=> v493(VarCurr,508) )
        & ( v574(VarCurr,15)
        <=> v493(VarCurr,507) )
        & ( v574(VarCurr,14)
        <=> v493(VarCurr,506) )
        & ( v574(VarCurr,13)
        <=> v493(VarCurr,505) )
        & ( v574(VarCurr,12)
        <=> v493(VarCurr,504) )
        & ( v574(VarCurr,11)
        <=> v493(VarCurr,503) )
        & ( v574(VarCurr,10)
        <=> v493(VarCurr,502) )
        & ( v574(VarCurr,9)
        <=> v493(VarCurr,501) )
        & ( v574(VarCurr,8)
        <=> v493(VarCurr,500) )
        & ( v574(VarCurr,7)
        <=> v493(VarCurr,499) )
        & ( v574(VarCurr,6)
        <=> v493(VarCurr,498) )
        & ( v574(VarCurr,5)
        <=> v493(VarCurr,497) )
        & ( v574(VarCurr,4)
        <=> v493(VarCurr,496) )
        & ( v574(VarCurr,3)
        <=> v493(VarCurr,495) )
        & ( v574(VarCurr,2)
        <=> v493(VarCurr,494) )
        & ( v574(VarCurr,1)
        <=> v493(VarCurr,493) )
        & ( v574(VarCurr,0)
        <=> v493(VarCurr,492) ) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_62,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v546(VarNext)
      <=> ( v547(VarNext)
          & v554(VarNext) ) ) ) ).

tff(addAssignment_154,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v554(VarNext)
      <=> v552(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_61,axiom,
    ! [VarCurr: state_type] :
      ( v552(VarCurr)
    <=> ( v555(VarCurr)
        & v567(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_60,axiom,
    ! [VarCurr: state_type] :
      ( v567(VarCurr)
    <=> ( v568(VarCurr)
        | v556(VarCurr) ) ) ).

tff(writeUnaryOperator_40,axiom,
    ! [VarCurr: state_type] :
      ( ~ v568(VarCurr)
    <=> v569(VarCurr) ) ).

tff(addBitVectorEqualityBitBlasted_30,axiom,
    ! [VarCurr: state_type] :
      ( v569(VarCurr)
    <=> ( ( v570(VarCurr,1)
        <=> $false )
        & ( v570(VarCurr,0)
        <=> $false ) ) ) ).

tff(addAssignment_153,axiom,
    ! [VarCurr: state_type] :
      ( v570(VarCurr,0)
    <=> v114(VarCurr) ) ).

tff(addAssignment_152,axiom,
    ! [VarCurr: state_type] :
      ( v570(VarCurr,1)
    <=> v96(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_59,axiom,
    ! [VarCurr: state_type] :
      ( v555(VarCurr)
    <=> ( v556(VarCurr)
        | v557(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_58,axiom,
    ! [VarCurr: state_type] :
      ( v557(VarCurr)
    <=> ( v558(VarCurr)
        & v566(VarCurr) ) ) ).

tff(writeUnaryOperator_39,axiom,
    ! [VarCurr: state_type] :
      ( ~ v566(VarCurr)
    <=> v556(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_57,axiom,
    ! [VarCurr: state_type] :
      ( v558(VarCurr)
    <=> ( v559(VarCurr)
        | v564(VarCurr) ) ) ).

tff(addBitVectorEqualityBitBlasted_29,axiom,
    ! [VarCurr: state_type] :
      ( v564(VarCurr)
    <=> ( ( v565(VarCurr,1)
        <=> $true )
        & ( v565(VarCurr,0)
        <=> $true ) ) ) ).

tff(addAssignment_151,axiom,
    ! [VarCurr: state_type] :
      ( v565(VarCurr,0)
    <=> v114(VarCurr) ) ).

tff(addAssignment_150,axiom,
    ! [VarCurr: state_type] :
      ( v565(VarCurr,1)
    <=> v96(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_56,axiom,
    ! [VarCurr: state_type] :
      ( v559(VarCurr)
    <=> ( v560(VarCurr)
        | v562(VarCurr) ) ) ).

tff(addBitVectorEqualityBitBlasted_28,axiom,
    ! [VarCurr: state_type] :
      ( v562(VarCurr)
    <=> ( ( v563(VarCurr,1)
        <=> $true )
        & ( v563(VarCurr,0)
        <=> $false ) ) ) ).

tff(addAssignment_149,axiom,
    ! [VarCurr: state_type] :
      ( v563(VarCurr,0)
    <=> v114(VarCurr) ) ).

tff(addAssignment_148,axiom,
    ! [VarCurr: state_type] :
      ( v563(VarCurr,1)
    <=> v96(VarCurr) ) ).

tff(addBitVectorEqualityBitBlasted_27,axiom,
    ! [VarCurr: state_type] :
      ( v560(VarCurr)
    <=> ( ( v561(VarCurr,1)
        <=> $false )
        & ( v561(VarCurr,0)
        <=> $true ) ) ) ).

tff(addAssignment_147,axiom,
    ! [VarCurr: state_type] :
      ( v561(VarCurr,0)
    <=> v114(VarCurr) ) ).

tff(addAssignment_146,axiom,
    ! [VarCurr: state_type] :
      ( v561(VarCurr,1)
    <=> v96(VarCurr) ) ).

tff(writeUnaryOperator_38,axiom,
    ! [VarCurr: state_type] :
      ( ~ v556(VarCurr)
    <=> v94(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_55,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v547(VarNext)
      <=> ( v548(VarNext)
          & v459(VarNext) ) ) ) ).

tff(writeUnaryOperator_37,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v548(VarNext)
      <=> v466(VarNext) ) ) ).

tff(addAssignment_145,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,123)
        & ~ $less(B,116) )
     => ( v538(VarCurr,B)
      <=> v543(VarCurr,B) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_16,axiom,
    ! [VarCurr: state_type] :
      ( ~ v540(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,123)
            & ~ $less(B,0) )
         => ( v543(VarCurr,B)
          <=> v542(VarCurr,B) ) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_16,axiom,
    ! [VarCurr: state_type] :
      ( v540(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,123)
            & ~ $less(B,0) )
         => ( v543(VarCurr,B)
          <=> v519(VarCurr,B) ) ) ) ).

tff(addAssignment_144,axiom,
    ! [VarCurr: state_type] :
      ( ( v542(VarCurr,122)
      <=> v493(VarCurr,614) )
      & ( v542(VarCurr,121)
      <=> v493(VarCurr,613) )
      & ( v542(VarCurr,120)
      <=> v493(VarCurr,612) )
      & ( v542(VarCurr,119)
      <=> v493(VarCurr,611) )
      & ( v542(VarCurr,118)
      <=> v493(VarCurr,610) )
      & ( v542(VarCurr,117)
      <=> v493(VarCurr,609) )
      & ( v542(VarCurr,116)
      <=> v493(VarCurr,608) ) ) ).

tff(addAssignment_143,axiom,
    ! [VarCurr: state_type] :
      ( v540(VarCurr)
    <=> v500(VarCurr,1) ) ).

tff(addAssignment_142,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,123)
        & ~ $less(B,116) )
     => ( v496(VarCurr,B)
      <=> v536(VarCurr,B) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_15,axiom,
    ! [VarCurr: state_type] :
      ( ~ v498(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,123)
            & ~ $less(B,0) )
         => ( v536(VarCurr,B)
          <=> v535(VarCurr,B) ) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_15,axiom,
    ! [VarCurr: state_type] :
      ( v498(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,123)
            & ~ $less(B,0) )
         => ( v536(VarCurr,B)
          <=> v519(VarCurr,B) ) ) ) ).

tff(addAssignment_141,axiom,
    ! [VarCurr: state_type] :
      ( ( v535(VarCurr,122)
      <=> v493(VarCurr,737) )
      & ( v535(VarCurr,121)
      <=> v493(VarCurr,736) )
      & ( v535(VarCurr,120)
      <=> v493(VarCurr,735) )
      & ( v535(VarCurr,119)
      <=> v493(VarCurr,734) )
      & ( v535(VarCurr,118)
      <=> v493(VarCurr,733) )
      & ( v535(VarCurr,117)
      <=> v493(VarCurr,732) )
      & ( v535(VarCurr,116)
      <=> v493(VarCurr,731) ) ) ).

tff(addAssignment_140,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,123)
        & ~ $less(B,116) )
     => ( v519(VarCurr,B)
      <=> v521(VarCurr,B) ) ) ).

tff(addAssignment_139,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,123)
        & ~ $less(B,116) )
     => ( v521(VarCurr,B)
      <=> v523(VarCurr,B) ) ) ).

tff(addAssignment_138,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,123)
        & ~ $less(B,116) )
     => ( v523(VarCurr,B)
      <=> v525(VarCurr,B) ) ) ).

tff(addAssignment_137,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,123)
        & ~ $less(B,116) )
     => ( v525(VarCurr,B)
      <=> v527(VarCurr,B) ) ) ).

tff(addAssignment_136,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,123)
        & ~ $less(B,116) )
     => ( v527(VarCurr,B)
      <=> v529(VarCurr,B) ) ) ).

tff(addAssignment_135,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,123)
        & ~ $less(B,116) )
     => ( v529(VarCurr,B)
      <=> v531(VarCurr,B) ) ) ).

tff(addAssignment_134,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,123)
        & ~ $less(B,116) )
     => ( v531(VarCurr,B)
      <=> v533(VarCurr,B) ) ) ).

tff(addAssignment_133,axiom,
    ! [VarCurr: state_type] :
      ( v498(VarCurr)
    <=> v500(VarCurr,1) ) ).

tff(addAssignment_132,axiom,
    ! [VarCurr: state_type] :
      ( v500(VarCurr,1)
    <=> v502(VarCurr,1) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_14,axiom,
    ! [VarCurr: state_type] :
      ( ~ v503(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,9)
            & ~ $less(B,0) )
         => ( v502(VarCurr,B)
          <=> v505(VarCurr,B) ) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_14,axiom,
    ! [VarCurr: state_type] :
      ( v503(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,9)
            & ~ $less(B,0) )
         => ( v502(VarCurr,B)
          <=> v504(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges3_1,axiom,
    ! [VarCurr: state_type] :
      ( ( ~ v506(VarCurr)
        & ~ v508(VarCurr)
        & ~ v512(VarCurr) )
     => ! [B: $int] :
          ( ( $less(B,9)
            & ~ $less(B,0) )
         => ( v505(VarCurr,B)
          <=> v456(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges2_3,axiom,
    ! [VarCurr: state_type] :
      ( v512(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,9)
            & ~ $less(B,0) )
         => ( v505(VarCurr,B)
          <=> v514(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_7,axiom,
    ! [VarCurr: state_type] :
      ( v508(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,9)
            & ~ $less(B,0) )
         => ( v505(VarCurr,B)
          <=> v510(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_7,axiom,
    ! [VarCurr: state_type] :
      ( v506(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,9)
            & ~ $less(B,0) )
         => ( v505(VarCurr,B)
          <=> v456(VarCurr,B) ) ) ) ).

tff(addBitVectorEqualityBitBlasted_26,axiom,
    ! [VarCurr: state_type] :
      ( v516(VarCurr)
    <=> ( ( v517(VarCurr,1)
        <=> $true )
        & ( v517(VarCurr,0)
        <=> $true ) ) ) ).

tff(addAssignment_131,axiom,
    ! [VarCurr: state_type] :
      ( v517(VarCurr,0)
    <=> v114(VarCurr) ) ).

tff(addAssignment_130,axiom,
    ! [VarCurr: state_type] :
      ( v517(VarCurr,1)
    <=> v96(VarCurr) ) ).

tff(addAssignment_129,axiom,
    ! [VarCurr: state_type] :
      ( v514(VarCurr,0)
    <=> $false ) ).

tff(addAssignment_128,axiom,
    ! [VarCurr: state_type] :
      ( ( v514(VarCurr,8)
      <=> v456(VarCurr,7) )
      & ( v514(VarCurr,7)
      <=> v456(VarCurr,6) )
      & ( v514(VarCurr,6)
      <=> v456(VarCurr,5) )
      & ( v514(VarCurr,5)
      <=> v456(VarCurr,4) )
      & ( v514(VarCurr,4)
      <=> v456(VarCurr,3) )
      & ( v514(VarCurr,3)
      <=> v456(VarCurr,2) )
      & ( v514(VarCurr,2)
      <=> v456(VarCurr,1) )
      & ( v514(VarCurr,1)
      <=> v456(VarCurr,0) ) ) ).

tff(addBitVectorEqualityBitBlasted_25,axiom,
    ! [VarCurr: state_type] :
      ( v512(VarCurr)
    <=> ( ( v513(VarCurr,1)
        <=> $true )
        & ( v513(VarCurr,0)
        <=> $false ) ) ) ).

tff(addAssignment_127,axiom,
    ! [VarCurr: state_type] :
      ( v513(VarCurr,0)
    <=> v114(VarCurr) ) ).

tff(addAssignment_126,axiom,
    ! [VarCurr: state_type] :
      ( v513(VarCurr,1)
    <=> v96(VarCurr) ) ).

tff(addAssignment_125,axiom,
    ! [VarCurr: state_type] :
      ( ( v510(VarCurr,7)
      <=> v456(VarCurr,8) )
      & ( v510(VarCurr,6)
      <=> v456(VarCurr,7) )
      & ( v510(VarCurr,5)
      <=> v456(VarCurr,6) )
      & ( v510(VarCurr,4)
      <=> v456(VarCurr,5) )
      & ( v510(VarCurr,3)
      <=> v456(VarCurr,4) )
      & ( v510(VarCurr,2)
      <=> v456(VarCurr,3) )
      & ( v510(VarCurr,1)
      <=> v456(VarCurr,2) )
      & ( v510(VarCurr,0)
      <=> v456(VarCurr,1) ) ) ).

tff(addAssignment_124,axiom,
    ! [VarCurr: state_type] :
      ( v510(VarCurr,8)
    <=> $false ) ).

tff(addBitVectorEqualityBitBlasted_24,axiom,
    ! [VarCurr: state_type] :
      ( v508(VarCurr)
    <=> ( ( v509(VarCurr,1)
        <=> $false )
        & ( v509(VarCurr,0)
        <=> $true ) ) ) ).

tff(addAssignment_123,axiom,
    ! [VarCurr: state_type] :
      ( v509(VarCurr,0)
    <=> v114(VarCurr) ) ).

tff(addAssignment_122,axiom,
    ! [VarCurr: state_type] :
      ( v509(VarCurr,1)
    <=> v96(VarCurr) ) ).

tff(addBitVectorEqualityBitBlasted_23,axiom,
    ! [VarCurr: state_type] :
      ( v506(VarCurr)
    <=> ( ( v507(VarCurr,1)
        <=> $false )
        & ( v507(VarCurr,0)
        <=> $false ) ) ) ).

tff(addAssignment_121,axiom,
    ! [VarCurr: state_type] :
      ( v507(VarCurr,0)
    <=> v114(VarCurr) ) ).

tff(addAssignment_120,axiom,
    ! [VarCurr: state_type] :
      ( v507(VarCurr,1)
    <=> v96(VarCurr) ) ).

tff(addAssignment_119,axiom,
    ! [VarCurr: state_type] :
      ( v504(VarCurr,0)
    <=> $true ) ).

tff(addAssignment_118,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,9)
        & ~ $less(B,1) )
     => ( v504(VarCurr,B)
      <=> v454(VarCurr,B) ) ) ).

tff(writeUnaryOperator_36,axiom,
    ! [VarCurr: state_type] :
      ( ~ v503(VarCurr)
    <=> v94(VarCurr) ) ).

tff(addAssignment_117,axiom,
    ! [VarCurr: state_type] :
      ( v454(VarCurr,1)
    <=> v455(VarCurr,1) ) ).

tff(addAssignment_116,axiom,
    ! [VarCurr: state_type] :
      ( v90(VarCurr)
    <=> v92(VarCurr) ) ).

tff(addCaseBooleanConditionEqualRanges1_2,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v462(VarNext)
       => ( v92(VarNext)
        <=> v92(VarCurr) ) ) ) ).

tff(addCaseBooleanConditionEqualRanges0_2,axiom,
    ! [VarNext: state_type] :
      ( v462(VarNext)
     => ( v92(VarNext)
      <=> v482(VarNext) ) ) ).

tff(addAssignment_115,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v482(VarNext)
      <=> v480(VarCurr) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_13,axiom,
    ! [VarCurr: state_type] :
      ( ~ v479(VarCurr)
     => ( v480(VarCurr)
      <=> v483(VarCurr) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_13,axiom,
    ! [VarCurr: state_type] :
      ( v479(VarCurr)
     => ( v480(VarCurr)
      <=> $true ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_12,axiom,
    ! [VarCurr: state_type] :
      ( ~ v96(VarCurr)
     => ( v483(VarCurr)
      <=> $true ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_12,axiom,
    ! [VarCurr: state_type] :
      ( v96(VarCurr)
     => ( v483(VarCurr)
      <=> $false ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_54,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v462(VarNext)
      <=> ( v463(VarNext)
          & v472(VarNext) ) ) ) ).

tff(addAssignment_114,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v472(VarNext)
      <=> v470(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_53,axiom,
    ! [VarCurr: state_type] :
      ( v470(VarCurr)
    <=> ( v473(VarCurr)
        | v479(VarCurr) ) ) ).

tff(writeUnaryOperator_35,axiom,
    ! [VarCurr: state_type] :
      ( ~ v479(VarCurr)
    <=> v94(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_52,axiom,
    ! [VarCurr: state_type] :
      ( v473(VarCurr)
    <=> ( v474(VarCurr)
        | v96(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_51,axiom,
    ! [VarCurr: state_type] :
      ( v474(VarCurr)
    <=> ( v475(VarCurr)
        & v478(VarCurr) ) ) ).

tff(addBitVectorEqualityBitBlasted_22,axiom,
    ! [VarCurr: state_type] :
      ( v478(VarCurr)
    <=> ( v454(VarCurr,0)
      <=> $true ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_50,axiom,
    ! [VarCurr: state_type] :
      ( v475(VarCurr)
    <=> ( v476(VarCurr)
        & v477(VarCurr) ) ) ).

tff(addBitVectorEqualityBitBlasted_21,axiom,
    ! [VarCurr: state_type] :
      ( v477(VarCurr)
    <=> ( v452(VarCurr,1)
      <=> $false ) ) ).

tff(addBitVectorEqualityBitBlasted_20,axiom,
    ! [VarCurr: state_type] :
      ( v476(VarCurr)
    <=> ( v114(VarCurr)
      <=> $true ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_49,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v463(VarNext)
      <=> ( v464(VarNext)
          & v459(VarNext) ) ) ) ).

tff(writeUnaryOperator_34,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v464(VarNext)
      <=> v466(VarNext) ) ) ).

tff(addAssignment_113,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v466(VarNext)
      <=> v459(VarCurr) ) ) ).

tff(addAssignment_112,axiom,
    ! [VarCurr: state_type] :
      ( v459(VarCurr)
    <=> v328(VarCurr) ) ).

tff(addAssignment_111,axiom,
    ! [VarCurr: state_type] :
      ( v454(VarCurr,0)
    <=> v455(VarCurr,0) ) ).

tff(addAssignment_110,axiom,
    ! [VarCurr: state_type] :
      ( v455(VarCurr,0)
    <=> $true ) ).

tff(addAssignment_109,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,9)
        & ~ $less(B,1) )
     => ( v455(VarCurr,B)
      <=> v456(VarCurr,B) ) ) ).

tff(addAssignment_108,axiom,
    ! [VarCurr: state_type] :
      ( v114(VarCurr)
    <=> v116(VarCurr) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_11,axiom,
    ! [VarCurr: state_type] :
      ( ~ v438(VarCurr)
     => ( v116(VarCurr)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_11,axiom,
    ! [VarCurr: state_type] :
      ( v438(VarCurr)
     => ( v116(VarCurr)
      <=> v447(VarCurr) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_6,axiom,
    ! [VarCurr: state_type] :
      ( ~ v440(VarCurr)
     => ( v447(VarCurr)
      <=> $false ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_6,axiom,
    ! [VarCurr: state_type] :
      ( v440(VarCurr)
     => ( v447(VarCurr)
      <=> v448(VarCurr) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges2_2,axiom,
    ! [VarCurr: state_type] :
      ( ( ~ v443(VarCurr)
        & ~ v271(VarCurr) )
     => ( v448(VarCurr)
      <=> $true ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_5,axiom,
    ! [VarCurr: state_type] :
      ( v271(VarCurr)
     => ( v448(VarCurr)
      <=> v450(VarCurr) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_5,axiom,
    ! [VarCurr: state_type] :
      ( v443(VarCurr)
     => ( v448(VarCurr)
      <=> v449(VarCurr) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_10,axiom,
    ! [VarCurr: state_type] :
      ( ~ v158(VarCurr)
     => ( v450(VarCurr)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_10,axiom,
    ! [VarCurr: state_type] :
      ( v158(VarCurr)
     => ( v450(VarCurr)
      <=> $true ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_9,axiom,
    ! [VarCurr: state_type] :
      ( ~ v431(VarCurr)
     => ( v449(VarCurr)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_9,axiom,
    ! [VarCurr: state_type] :
      ( v431(VarCurr)
     => ( v449(VarCurr)
      <=> $true ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_48,axiom,
    ! [VarCurr: state_type] :
      ( v438(VarCurr)
    <=> ( v439(VarCurr)
        & v446(VarCurr) ) ) ).

tff(writeUnaryOperator_33,axiom,
    ! [VarCurr: state_type] :
      ( ~ v446(VarCurr)
    <=> v275(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_47,axiom,
    ! [VarCurr: state_type] :
      ( v439(VarCurr)
    <=> ( v440(VarCurr)
        | v445(VarCurr) ) ) ).

tff(writeUnaryOperator_32,axiom,
    ! [VarCurr: state_type] :
      ( ~ v445(VarCurr)
    <=> v272(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_46,axiom,
    ! [VarCurr: state_type] :
      ( v440(VarCurr)
    <=> ( v441(VarCurr)
        & v272(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_45,axiom,
    ! [VarCurr: state_type] :
      ( v441(VarCurr)
    <=> ( v442(VarCurr)
        | v444(VarCurr) ) ) ).

tff(addBitVectorEqualityBitBlasted_19,axiom,
    ! [VarCurr: state_type] :
      ( v444(VarCurr)
    <=> ( ( v88(VarCurr,1)
        <=> $true )
        & ( v88(VarCurr,0)
        <=> $false ) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_44,axiom,
    ! [VarCurr: state_type] :
      ( v442(VarCurr)
    <=> ( v443(VarCurr)
        | v271(VarCurr) ) ) ).

tff(addBitVectorEqualityBitBlasted_18,axiom,
    ! [VarCurr: state_type] :
      ( v443(VarCurr)
    <=> ( ( v88(VarCurr,1)
        <=> $false )
        & ( v88(VarCurr,0)
        <=> $false ) ) ) ).

tff(writeBinaryOperatorShiftedRanges_21,axiom,
    ! [VarCurr: state_type] :
      ( v431(VarCurr)
    <=> ( v436(VarCurr)
        | v433(VarCurr,2) ) ) ).

tff(writeBinaryOperatorShiftedRanges_20,axiom,
    ! [VarCurr: state_type] :
      ( v436(VarCurr)
    <=> ( v433(VarCurr,0)
        | v433(VarCurr,1) ) ) ).

tff(addAssignment_107,axiom,
    ! [VarCurr: state_type] :
      ( v121(VarCurr)
    <=> v123(VarCurr) ) ).

tff(addBitVectorEqualityBitBlasted_17,axiom,
    ! [VarCurr: state_type] :
      ( v123(VarCurr)
    <=> ( ( v125(VarCurr,2)
        <=> $false )
        & ( v125(VarCurr,1)
        <=> $false )
        & ( v125(VarCurr,0)
        <=> $false ) ) ) ).

tff(addCaseBooleanConditionEqualRanges1_1,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v415(VarNext)
       => ! [B: $int] :
            ( ( $less(B,3)
              & ~ $less(B,0) )
           => ( v125(VarNext,B)
            <=> v125(VarCurr,B) ) ) ) ) ).

tff(addCaseBooleanConditionEqualRanges0_1,axiom,
    ! [VarNext: state_type] :
      ( v415(VarNext)
     => ! [B: $int] :
          ( ( $less(B,3)
            & ~ $less(B,0) )
         => ( v125(VarNext,B)
          <=> v425(VarNext,B) ) ) ) ).

tff(addAssignment_106,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ! [B: $int] :
          ( ( $less(B,3)
            & ~ $less(B,0) )
         => ( v425(VarNext,B)
          <=> v423(VarCurr,B) ) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_8,axiom,
    ! [VarCurr: state_type] :
      ( ~ v426(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,3)
            & ~ $less(B,0) )
         => ( v423(VarCurr,B)
          <=> v130(VarCurr,B) ) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_8,axiom,
    ! [VarCurr: state_type] :
      ( v426(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,3)
            & ~ $less(B,0) )
         => ( v423(VarCurr,B)
          <=> $false ) ) ) ).

tff(writeUnaryOperator_31,axiom,
    ! [VarCurr: state_type] :
      ( ~ v426(VarCurr)
    <=> v127(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_43,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v415(VarNext)
      <=> v416(VarNext) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_42,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v416(VarNext)
      <=> ( v417(VarNext)
          & v412(VarNext) ) ) ) ).

tff(writeUnaryOperator_30,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v417(VarNext)
      <=> v419(VarNext) ) ) ).

tff(addAssignment_105,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v419(VarNext)
      <=> v412(VarCurr) ) ) ).

tff(addAssignment_104,axiom,
    ! [VarCurr: state_type] :
      ( v412(VarCurr)
    <=> v328(VarCurr) ) ).

tff(addParallelCaseBooleanConditionEqualRanges3,axiom,
    ! [VarCurr: state_type] :
      ( ( ~ v361(VarCurr)
        & ~ v363(VarCurr)
        & ~ v392(VarCurr) )
     => ! [B: $int] :
          ( ( $less(B,3)
            & ~ $less(B,0) )
         => ( v130(VarCurr,B)
          <=> v125(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges2_1,axiom,
    ! [VarCurr: state_type] :
      ( v392(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,3)
            & ~ $less(B,0) )
         => ( v130(VarCurr,B)
          <=> v394(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_4,axiom,
    ! [VarCurr: state_type] :
      ( v363(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,3)
            & ~ $less(B,0) )
         => ( v130(VarCurr,B)
          <=> v365(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_4,axiom,
    ! [VarCurr: state_type] :
      ( v361(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,3)
            & ~ $less(B,0) )
         => ( v130(VarCurr,B)
          <=> v125(VarCurr,B) ) ) ) ).

tff(addBitVectorEqualityBitBlasted_16,axiom,
    ! [VarCurr: state_type] :
      ( v409(VarCurr)
    <=> ( ( v410(VarCurr,1)
        <=> $true )
        & ( v410(VarCurr,0)
        <=> $true ) ) ) ).

tff(addAssignment_103,axiom,
    ! [VarCurr: state_type] :
      ( v410(VarCurr,0)
    <=> v152(VarCurr) ) ).

tff(addAssignment_102,axiom,
    ! [VarCurr: state_type] :
      ( v410(VarCurr,1)
    <=> v132(VarCurr) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_7,axiom,
    ! [VarCurr: state_type] :
      ( ~ v395(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,3)
            & ~ $less(B,0) )
         => ( v394(VarCurr,B)
          <=> v396(VarCurr,B) ) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_7,axiom,
    ! [VarCurr: state_type] :
      ( v395(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,3)
            & ~ $less(B,0) )
         => ( v394(VarCurr,B)
          <=> b100(B) ) ) ) ).

tff(addAssignment_101,axiom,
    ! [VarCurr: state_type] :
      ( v396(VarCurr,0)
    <=> v406(VarCurr) ) ).

tff(addAssignment_100,axiom,
    ! [VarCurr: state_type] :
      ( v396(VarCurr,1)
    <=> v404(VarCurr) ) ).

tff(addAssignment_99,axiom,
    ! [VarCurr: state_type] :
      ( v396(VarCurr,2)
    <=> v398(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_41,axiom,
    ! [VarCurr: state_type] :
      ( v404(VarCurr)
    <=> ( v405(VarCurr)
        & v408(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_19,axiom,
    ! [VarCurr: state_type] :
      ( v408(VarCurr)
    <=> ( v125(VarCurr,0)
        | v125(VarCurr,1) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_40,axiom,
    ! [VarCurr: state_type] :
      ( v405(VarCurr)
    <=> ( v406(VarCurr)
        | v407(VarCurr) ) ) ).

tff(writeUnaryOperator_29,axiom,
    ! [VarCurr: state_type] :
      ( ~ v407(VarCurr)
    <=> v125(VarCurr,1) ) ).

tff(writeUnaryOperator_28,axiom,
    ! [VarCurr: state_type] :
      ( ~ v406(VarCurr)
    <=> v125(VarCurr,0) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_39,axiom,
    ! [VarCurr: state_type] :
      ( v398(VarCurr)
    <=> ( v399(VarCurr)
        & v403(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_18,axiom,
    ! [VarCurr: state_type] :
      ( v403(VarCurr)
    <=> ( v401(VarCurr)
        | v125(VarCurr,2) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_38,axiom,
    ! [VarCurr: state_type] :
      ( v399(VarCurr)
    <=> ( v400(VarCurr)
        | v402(VarCurr) ) ) ).

tff(writeUnaryOperator_27,axiom,
    ! [VarCurr: state_type] :
      ( ~ v402(VarCurr)
    <=> v125(VarCurr,2) ) ).

tff(writeUnaryOperator_26,axiom,
    ! [VarCurr: state_type] :
      ( ~ v400(VarCurr)
    <=> v401(VarCurr) ) ).

tff(writeBinaryOperatorShiftedRanges_17,axiom,
    ! [VarCurr: state_type] :
      ( v401(VarCurr)
    <=> ( v125(VarCurr,0)
        & v125(VarCurr,1) ) ) ).

tff(addBitVectorEqualityBitBlasted_15,axiom,
    ! [VarCurr: state_type] :
      ( v395(VarCurr)
    <=> ( ( v125(VarCurr,2)
        <=> $true )
        & ( v125(VarCurr,1)
        <=> $false )
        & ( v125(VarCurr,0)
        <=> $false ) ) ) ).

tff(bitBlastConstant_59,axiom,
    b100(2) ).

tff(bitBlastConstant_58,axiom,
    ~ b100(1) ).

tff(bitBlastConstant_57,axiom,
    ~ b100(0) ).

tff(addBitVectorEqualityBitBlasted_14,axiom,
    ! [VarCurr: state_type] :
      ( v392(VarCurr)
    <=> ( ( v393(VarCurr,1)
        <=> $true )
        & ( v393(VarCurr,0)
        <=> $false ) ) ) ).

tff(addAssignment_98,axiom,
    ! [VarCurr: state_type] :
      ( v393(VarCurr,0)
    <=> v152(VarCurr) ) ).

tff(addAssignment_97,axiom,
    ! [VarCurr: state_type] :
      ( v393(VarCurr,1)
    <=> v132(VarCurr) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_6,axiom,
    ! [VarCurr: state_type] :
      ( ~ v366(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,32)
            & ~ $less(B,0) )
         => ( v365(VarCurr,B)
          <=> v367(VarCurr,B) ) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_6,axiom,
    ! [VarCurr: state_type] :
      ( v366(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,32)
            & ~ $less(B,0) )
         => ( v365(VarCurr,B)
          <=> $false ) ) ) ).

tff(bitBlastConstant_56,axiom,
    ~ b00000000000000000000000000000000(31) ).

tff(bitBlastConstant_55,axiom,
    ~ b00000000000000000000000000000000(30) ).

tff(bitBlastConstant_54,axiom,
    ~ b00000000000000000000000000000000(29) ).

tff(bitBlastConstant_53,axiom,
    ~ b00000000000000000000000000000000(28) ).

tff(bitBlastConstant_52,axiom,
    ~ b00000000000000000000000000000000(27) ).

tff(bitBlastConstant_51,axiom,
    ~ b00000000000000000000000000000000(26) ).

tff(bitBlastConstant_50,axiom,
    ~ b00000000000000000000000000000000(25) ).

tff(bitBlastConstant_49,axiom,
    ~ b00000000000000000000000000000000(24) ).

tff(bitBlastConstant_48,axiom,
    ~ b00000000000000000000000000000000(23) ).

tff(bitBlastConstant_47,axiom,
    ~ b00000000000000000000000000000000(22) ).

tff(bitBlastConstant_46,axiom,
    ~ b00000000000000000000000000000000(21) ).

tff(bitBlastConstant_45,axiom,
    ~ b00000000000000000000000000000000(20) ).

tff(bitBlastConstant_44,axiom,
    ~ b00000000000000000000000000000000(19) ).

tff(bitBlastConstant_43,axiom,
    ~ b00000000000000000000000000000000(18) ).

tff(bitBlastConstant_42,axiom,
    ~ b00000000000000000000000000000000(17) ).

tff(bitBlastConstant_41,axiom,
    ~ b00000000000000000000000000000000(16) ).

tff(bitBlastConstant_40,axiom,
    ~ b00000000000000000000000000000000(15) ).

tff(bitBlastConstant_39,axiom,
    ~ b00000000000000000000000000000000(14) ).

tff(bitBlastConstant_38,axiom,
    ~ b00000000000000000000000000000000(13) ).

tff(bitBlastConstant_37,axiom,
    ~ b00000000000000000000000000000000(12) ).

tff(bitBlastConstant_36,axiom,
    ~ b00000000000000000000000000000000(11) ).

tff(bitBlastConstant_35,axiom,
    ~ b00000000000000000000000000000000(10) ).

tff(bitBlastConstant_34,axiom,
    ~ b00000000000000000000000000000000(9) ).

tff(bitBlastConstant_33,axiom,
    ~ b00000000000000000000000000000000(8) ).

tff(bitBlastConstant_32,axiom,
    ~ b00000000000000000000000000000000(7) ).

tff(bitBlastConstant_31,axiom,
    ~ b00000000000000000000000000000000(6) ).

tff(bitBlastConstant_30,axiom,
    ~ b00000000000000000000000000000000(5) ).

tff(bitBlastConstant_29,axiom,
    ~ b00000000000000000000000000000000(4) ).

tff(bitBlastConstant_28,axiom,
    ~ b00000000000000000000000000000000(3) ).

tff(bitBlastConstant_27,axiom,
    ~ b00000000000000000000000000000000(2) ).

tff(bitBlastConstant_26,axiom,
    ~ b00000000000000000000000000000000(1) ).

tff(bitBlastConstant_25,axiom,
    ~ b00000000000000000000000000000000(0) ).

tff(addSignExtensionConstraint_27,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,4)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_26,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,5)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_25,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,6)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_24,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,7)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_23,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,8)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_22,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,9)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_21,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,10)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_20,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,11)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_19,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,12)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_18,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,13)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_17,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,14)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_16,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,15)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_15,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,16)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_14,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,17)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_13,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,18)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_12,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,19)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_11,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,20)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_10,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,21)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_9,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,22)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_8,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,23)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_7,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,24)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_6,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,25)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_5,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,26)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_4,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,27)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_3,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,28)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_2,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,29)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint_1,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,30)
    <=> v368(VarCurr,3) ) ).

tff(addSignExtensionConstraint,axiom,
    ! [VarCurr: state_type] :
      ( v367(VarCurr,31)
    <=> v368(VarCurr,3) ) ).

tff(addAssignment_96,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,4)
        & ~ $less(B,0) )
     => ( v367(VarCurr,B)
      <=> v368(VarCurr,B) ) ) ).

tff(addAssignment_95,axiom,
    ! [VarCurr: state_type] :
      ( v368(VarCurr,0)
    <=> v389(VarCurr) ) ).

tff(addAssignment_94,axiom,
    ! [VarCurr: state_type] :
      ( v368(VarCurr,1)
    <=> v387(VarCurr) ) ).

tff(addAssignment_93,axiom,
    ! [VarCurr: state_type] :
      ( v368(VarCurr,2)
    <=> v383(VarCurr) ) ).

tff(addAssignment_92,axiom,
    ! [VarCurr: state_type] :
      ( v368(VarCurr,3)
    <=> v370(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_37,axiom,
    ! [VarCurr: state_type] :
      ( v387(VarCurr)
    <=> ( v388(VarCurr)
        & v390(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_36,axiom,
    ! [VarCurr: state_type] :
      ( v390(VarCurr)
    <=> ( v374(VarCurr,0)
        | v379(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_16,axiom,
    ! [VarCurr: state_type] :
      ( v388(VarCurr)
    <=> ( v389(VarCurr)
        | v374(VarCurr,1) ) ) ).

tff(writeUnaryOperator_25,axiom,
    ! [VarCurr: state_type] :
      ( ~ v389(VarCurr)
    <=> v374(VarCurr,0) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_35,axiom,
    ! [VarCurr: state_type] :
      ( v383(VarCurr)
    <=> ( v384(VarCurr)
        & v386(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_34,axiom,
    ! [VarCurr: state_type] :
      ( v386(VarCurr)
    <=> ( v377(VarCurr)
        | v380(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_15,axiom,
    ! [VarCurr: state_type] :
      ( v384(VarCurr)
    <=> ( v385(VarCurr)
        | v374(VarCurr,2) ) ) ).

tff(writeUnaryOperator_24,axiom,
    ! [VarCurr: state_type] :
      ( ~ v385(VarCurr)
    <=> v377(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_33,axiom,
    ! [VarCurr: state_type] :
      ( v370(VarCurr)
    <=> ( v371(VarCurr)
        & v381(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_32,axiom,
    ! [VarCurr: state_type] :
      ( v381(VarCurr)
    <=> ( v373(VarCurr)
        | v382(VarCurr) ) ) ).

tff(writeUnaryOperator_23,axiom,
    ! [VarCurr: state_type] :
      ( ~ v382(VarCurr)
    <=> v374(VarCurr,3) ) ).

tff(writeBinaryOperatorShiftedRanges_14,axiom,
    ! [VarCurr: state_type] :
      ( v371(VarCurr)
    <=> ( v372(VarCurr)
        | v374(VarCurr,3) ) ) ).

tff(writeUnaryOperator_22,axiom,
    ! [VarCurr: state_type] :
      ( ~ v372(VarCurr)
    <=> v373(VarCurr) ) ).

tff(writeBinaryOperatorShiftedRanges_13,axiom,
    ! [VarCurr: state_type] :
      ( v373(VarCurr)
    <=> ( v374(VarCurr,2)
        | v376(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_31,axiom,
    ! [VarCurr: state_type] :
      ( v376(VarCurr)
    <=> ( v377(VarCurr)
        & v380(VarCurr) ) ) ).

tff(writeUnaryOperator_21,axiom,
    ! [VarCurr: state_type] :
      ( ~ v380(VarCurr)
    <=> v374(VarCurr,2) ) ).

tff(writeBinaryOperatorShiftedRanges_12,axiom,
    ! [VarCurr: state_type] :
      ( v377(VarCurr)
    <=> ( v374(VarCurr,1)
        | v378(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_30,axiom,
    ! [VarCurr: state_type] :
      ( v378(VarCurr)
    <=> ( v374(VarCurr,0)
        & v379(VarCurr) ) ) ).

tff(writeUnaryOperator_20,axiom,
    ! [VarCurr: state_type] :
      ( ~ v379(VarCurr)
    <=> v374(VarCurr,1) ) ).

tff(addZeroExtensionConstraint,axiom,
    ! [VarCurr: state_type] : ~ v374(VarCurr,3) ).

tff(addAssignment_91,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,3)
        & ~ $less(B,0) )
     => ( v374(VarCurr,B)
      <=> v125(VarCurr,B) ) ) ).

tff(addBitVectorEqualityBitBlasted_13,axiom,
    ! [VarCurr: state_type] :
      ( v366(VarCurr)
    <=> ( ( v125(VarCurr,2)
        <=> $false )
        & ( v125(VarCurr,1)
        <=> $false )
        & ( v125(VarCurr,0)
        <=> $false ) ) ) ).

tff(bitBlastConstant_24,axiom,
    ~ b000(2) ).

tff(bitBlastConstant_23,axiom,
    ~ b000(1) ).

tff(bitBlastConstant_22,axiom,
    ~ b000(0) ).

tff(addBitVectorEqualityBitBlasted_12,axiom,
    ! [VarCurr: state_type] :
      ( v363(VarCurr)
    <=> ( ( v364(VarCurr,1)
        <=> $false )
        & ( v364(VarCurr,0)
        <=> $true ) ) ) ).

tff(addAssignment_90,axiom,
    ! [VarCurr: state_type] :
      ( v364(VarCurr,0)
    <=> v152(VarCurr) ) ).

tff(addAssignment_89,axiom,
    ! [VarCurr: state_type] :
      ( v364(VarCurr,1)
    <=> v132(VarCurr) ) ).

tff(addBitVectorEqualityBitBlasted_11,axiom,
    ! [VarCurr: state_type] :
      ( v361(VarCurr)
    <=> ( ( v362(VarCurr,1)
        <=> $false )
        & ( v362(VarCurr,0)
        <=> $false ) ) ) ).

tff(addAssignment_88,axiom,
    ! [VarCurr: state_type] :
      ( v362(VarCurr,0)
    <=> v152(VarCurr) ) ).

tff(addAssignment_87,axiom,
    ! [VarCurr: state_type] :
      ( v362(VarCurr,1)
    <=> v132(VarCurr) ) ).

tff(addAssignment_86,axiom,
    ! [VarCurr: state_type] :
      ( v152(VarCurr)
    <=> v154(VarCurr) ) ).

tff(addAssignment_85,axiom,
    ! [VarCurr: state_type] :
      ( v154(VarCurr)
    <=> v156(VarCurr) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_5,axiom,
    ! [VarCurr: state_type] :
      ( ~ v353(VarCurr)
     => ( v156(VarCurr)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_5,axiom,
    ! [VarCurr: state_type] :
      ( v353(VarCurr)
     => ( v156(VarCurr)
      <=> v357(VarCurr) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_3,axiom,
    ! [VarCurr: state_type] :
      ( ~ v275(VarCurr)
     => ( v357(VarCurr)
      <=> $false ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_3,axiom,
    ! [VarCurr: state_type] :
      ( v275(VarCurr)
     => ( v357(VarCurr)
      <=> $true ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_29,axiom,
    ! [VarCurr: state_type] :
      ( v353(VarCurr)
    <=> ( v275(VarCurr)
        | v354(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_28,axiom,
    ! [VarCurr: state_type] :
      ( v354(VarCurr)
    <=> ( v355(VarCurr)
        & v356(VarCurr) ) ) ).

tff(writeUnaryOperator_19,axiom,
    ! [VarCurr: state_type] :
      ( ~ v356(VarCurr)
    <=> v275(VarCurr) ) ).

tff(writeUnaryOperator_18,axiom,
    ! [VarCurr: state_type] :
      ( ~ v355(VarCurr)
    <=> v272(VarCurr) ) ).

tff(writeBinaryOperatorShiftedRanges_11,axiom,
    ! [VarCurr: state_type] :
      ( v158(VarCurr)
    <=> ( v351(VarCurr)
        | v160(VarCurr,3) ) ) ).

tff(writeBinaryOperatorShiftedRanges_10,axiom,
    ! [VarCurr: state_type] :
      ( v351(VarCurr)
    <=> ( v321(VarCurr)
        | v160(VarCurr,2) ) ) ).

tff(addCaseBooleanConditionEqualRanges1,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v335(VarNext)
       => ! [B: $int] :
            ( ( $less(B,4)
              & ~ $less(B,0) )
           => ( v160(VarNext,B)
            <=> v160(VarCurr,B) ) ) ) ) ).

tff(addCaseBooleanConditionEqualRanges0,axiom,
    ! [VarNext: state_type] :
      ( v335(VarNext)
     => ! [B: $int] :
          ( ( $less(B,4)
            & ~ $less(B,0) )
         => ( v160(VarNext,B)
          <=> v345(VarNext,B) ) ) ) ).

tff(addAssignment_84,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ! [B: $int] :
          ( ( $less(B,4)
            & ~ $less(B,0) )
         => ( v345(VarNext,B)
          <=> v343(VarCurr,B) ) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_4,axiom,
    ! [VarCurr: state_type] :
      ( ~ v346(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,4)
            & ~ $less(B,0) )
         => ( v343(VarCurr,B)
          <=> v163(VarCurr,B) ) ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_4,axiom,
    ! [VarCurr: state_type] :
      ( v346(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,4)
            & ~ $less(B,0) )
         => ( v343(VarCurr,B)
          <=> b1000(B) ) ) ) ).

tff(bitBlastConstant_21,axiom,
    b1000(3) ).

tff(bitBlastConstant_20,axiom,
    ~ b1000(2) ).

tff(bitBlastConstant_19,axiom,
    ~ b1000(1) ).

tff(bitBlastConstant_18,axiom,
    ~ b1000(0) ).

tff(writeUnaryOperator_17,axiom,
    ! [VarCurr: state_type] :
      ( ~ v346(VarCurr)
    <=> v82(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_27,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v335(VarNext)
      <=> v336(VarNext) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_26,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v336(VarNext)
      <=> ( v337(VarNext)
          & v328(VarNext) ) ) ) ).

tff(writeUnaryOperator_16,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( ~ v337(VarNext)
      <=> v339(VarNext) ) ) ).

tff(addAssignment_83,axiom,
    ! [VarNext: state_type,VarCurr: state_type] :
      ( nextState(VarCurr,VarNext)
     => ( v339(VarNext)
      <=> v328(VarCurr) ) ) ).

tff(addAssignment_82,axiom,
    ! [VarCurr: state_type] :
      ( v328(VarCurr)
    <=> v330(VarCurr) ) ).

tff(addAssignment_81,axiom,
    ! [VarCurr: state_type] :
      ( v330(VarCurr)
    <=> v332(VarCurr) ) ).

tff(addAssignment_80,axiom,
    ! [VarCurr: state_type] :
      ( v332(VarCurr)
    <=> v1(VarCurr) ) ).

tff(addParallelCaseBooleanConditionEqualRanges2,axiom,
    ! [VarCurr: state_type] :
      ( ( ~ v282(VarCurr)
        & ~ v305(VarCurr) )
     => ! [B: $int] :
          ( ( $less(B,4)
            & ~ $less(B,0) )
         => ( v163(VarCurr,B)
          <=> v160(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_2,axiom,
    ! [VarCurr: state_type] :
      ( v305(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,4)
            & ~ $less(B,0) )
         => ( v163(VarCurr,B)
          <=> v307(VarCurr,B) ) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_2,axiom,
    ! [VarCurr: state_type] :
      ( v282(VarCurr)
     => ! [B: $int] :
          ( ( $less(B,4)
            & ~ $less(B,0) )
         => ( v163(VarCurr,B)
          <=> v284(VarCurr,B) ) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_25,axiom,
    ! [VarCurr: state_type] :
      ( v322(VarCurr)
    <=> ( v323(VarCurr)
        | v325(VarCurr) ) ) ).

tff(addBitVectorEqualityBitBlasted_10,axiom,
    ! [VarCurr: state_type] :
      ( v325(VarCurr)
    <=> ( ( v326(VarCurr,1)
        <=> $true )
        & ( v326(VarCurr,0)
        <=> $true ) ) ) ).

tff(addAssignment_79,axiom,
    ! [VarCurr: state_type] :
      ( v326(VarCurr,0)
    <=> v264(VarCurr) ) ).

tff(addAssignment_78,axiom,
    ! [VarCurr: state_type] :
      ( v326(VarCurr,1)
    <=> v165(VarCurr) ) ).

tff(addBitVectorEqualityBitBlasted_9,axiom,
    ! [VarCurr: state_type] :
      ( v323(VarCurr)
    <=> ( ( v324(VarCurr,1)
        <=> $false )
        & ( v324(VarCurr,0)
        <=> $false ) ) ) ).

tff(bitBlastConstant_17,axiom,
    ~ b00(1) ).

tff(bitBlastConstant_16,axiom,
    ~ b00(0) ).

tff(addAssignment_77,axiom,
    ! [VarCurr: state_type] :
      ( v324(VarCurr,0)
    <=> v264(VarCurr) ) ).

tff(addAssignment_76,axiom,
    ! [VarCurr: state_type] :
      ( v324(VarCurr,1)
    <=> v165(VarCurr) ) ).

tff(addAssignment_75,axiom,
    ! [VarCurr: state_type] :
      ( v307(VarCurr,0)
    <=> v303(VarCurr) ) ).

tff(addAssignment_74,axiom,
    ! [VarCurr: state_type] :
      ( v307(VarCurr,1)
    <=> v319(VarCurr) ) ).

tff(addAssignment_73,axiom,
    ! [VarCurr: state_type] :
      ( v307(VarCurr,2)
    <=> v315(VarCurr) ) ).

tff(addAssignment_72,axiom,
    ! [VarCurr: state_type] :
      ( v307(VarCurr,3)
    <=> v309(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_24,axiom,
    ! [VarCurr: state_type] :
      ( v319(VarCurr)
    <=> ( v320(VarCurr)
        & v321(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_9,axiom,
    ! [VarCurr: state_type] :
      ( v321(VarCurr)
    <=> ( v160(VarCurr,0)
        | v160(VarCurr,1) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_23,axiom,
    ! [VarCurr: state_type] :
      ( v320(VarCurr)
    <=> ( v303(VarCurr)
        | v293(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_22,axiom,
    ! [VarCurr: state_type] :
      ( v315(VarCurr)
    <=> ( v316(VarCurr)
        & v318(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_8,axiom,
    ! [VarCurr: state_type] :
      ( v318(VarCurr)
    <=> ( v160(VarCurr,2)
        | v313(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_21,axiom,
    ! [VarCurr: state_type] :
      ( v316(VarCurr)
    <=> ( v294(VarCurr)
        | v317(VarCurr) ) ) ).

tff(writeUnaryOperator_15,axiom,
    ! [VarCurr: state_type] :
      ( ~ v317(VarCurr)
    <=> v313(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_20,axiom,
    ! [VarCurr: state_type] :
      ( v309(VarCurr)
    <=> ( v310(VarCurr)
        & v314(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_7,axiom,
    ! [VarCurr: state_type] :
      ( v314(VarCurr)
    <=> ( v160(VarCurr,3)
        | v312(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_19,axiom,
    ! [VarCurr: state_type] :
      ( v310(VarCurr)
    <=> ( v296(VarCurr)
        | v311(VarCurr) ) ) ).

tff(writeUnaryOperator_14,axiom,
    ! [VarCurr: state_type] :
      ( ~ v311(VarCurr)
    <=> v312(VarCurr) ) ).

tff(writeBinaryOperatorShiftedRanges_6,axiom,
    ! [VarCurr: state_type] :
      ( v312(VarCurr)
    <=> ( v160(VarCurr,2)
        & v313(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_5,axiom,
    ! [VarCurr: state_type] :
      ( v313(VarCurr)
    <=> ( v160(VarCurr,0)
        & v160(VarCurr,1) ) ) ).

tff(addBitVectorEqualityBitBlasted_8,axiom,
    ! [VarCurr: state_type] :
      ( v305(VarCurr)
    <=> ( ( v306(VarCurr,1)
        <=> $true )
        & ( v306(VarCurr,0)
        <=> $false ) ) ) ).

tff(bitBlastConstant_15,axiom,
    b10(1) ).

tff(bitBlastConstant_14,axiom,
    ~ b10(0) ).

tff(addAssignment_71,axiom,
    ! [VarCurr: state_type] :
      ( v306(VarCurr,0)
    <=> v264(VarCurr) ) ).

tff(addAssignment_70,axiom,
    ! [VarCurr: state_type] :
      ( v306(VarCurr,1)
    <=> v165(VarCurr) ) ).

tff(addAssignment_69,axiom,
    ! [VarCurr: state_type] :
      ( v284(VarCurr,0)
    <=> v303(VarCurr) ) ).

tff(addAssignment_68,axiom,
    ! [VarCurr: state_type] :
      ( v284(VarCurr,1)
    <=> v301(VarCurr) ) ).

tff(addAssignment_67,axiom,
    ! [VarCurr: state_type] :
      ( v284(VarCurr,2)
    <=> v297(VarCurr) ) ).

tff(addAssignment_66,axiom,
    ! [VarCurr: state_type] :
      ( v284(VarCurr,3)
    <=> v286(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_18,axiom,
    ! [VarCurr: state_type] :
      ( v301(VarCurr)
    <=> ( v302(VarCurr)
        & v304(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_17,axiom,
    ! [VarCurr: state_type] :
      ( v304(VarCurr)
    <=> ( v160(VarCurr,0)
        | v293(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_4,axiom,
    ! [VarCurr: state_type] :
      ( v302(VarCurr)
    <=> ( v303(VarCurr)
        | v160(VarCurr,1) ) ) ).

tff(writeUnaryOperator_13,axiom,
    ! [VarCurr: state_type] :
      ( ~ v303(VarCurr)
    <=> v160(VarCurr,0) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_16,axiom,
    ! [VarCurr: state_type] :
      ( v297(VarCurr)
    <=> ( v298(VarCurr)
        & v300(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_15,axiom,
    ! [VarCurr: state_type] :
      ( v300(VarCurr)
    <=> ( v291(VarCurr)
        | v294(VarCurr) ) ) ).

tff(writeBinaryOperatorShiftedRanges_3,axiom,
    ! [VarCurr: state_type] :
      ( v298(VarCurr)
    <=> ( v299(VarCurr)
        | v160(VarCurr,2) ) ) ).

tff(writeUnaryOperator_12,axiom,
    ! [VarCurr: state_type] :
      ( ~ v299(VarCurr)
    <=> v291(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_14,axiom,
    ! [VarCurr: state_type] :
      ( v286(VarCurr)
    <=> ( v287(VarCurr)
        & v295(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_13,axiom,
    ! [VarCurr: state_type] :
      ( v295(VarCurr)
    <=> ( v289(VarCurr)
        | v296(VarCurr) ) ) ).

tff(writeUnaryOperator_11,axiom,
    ! [VarCurr: state_type] :
      ( ~ v296(VarCurr)
    <=> v160(VarCurr,3) ) ).

tff(writeBinaryOperatorShiftedRanges_2,axiom,
    ! [VarCurr: state_type] :
      ( v287(VarCurr)
    <=> ( v288(VarCurr)
        | v160(VarCurr,3) ) ) ).

tff(writeUnaryOperator_10,axiom,
    ! [VarCurr: state_type] :
      ( ~ v288(VarCurr)
    <=> v289(VarCurr) ) ).

tff(writeBinaryOperatorShiftedRanges_1,axiom,
    ! [VarCurr: state_type] :
      ( v289(VarCurr)
    <=> ( v160(VarCurr,2)
        | v290(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_12,axiom,
    ! [VarCurr: state_type] :
      ( v290(VarCurr)
    <=> ( v291(VarCurr)
        & v294(VarCurr) ) ) ).

tff(writeUnaryOperator_9,axiom,
    ! [VarCurr: state_type] :
      ( ~ v294(VarCurr)
    <=> v160(VarCurr,2) ) ).

tff(writeBinaryOperatorShiftedRanges,axiom,
    ! [VarCurr: state_type] :
      ( v291(VarCurr)
    <=> ( v160(VarCurr,1)
        | v292(VarCurr) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_11,axiom,
    ! [VarCurr: state_type] :
      ( v292(VarCurr)
    <=> ( v160(VarCurr,0)
        & v293(VarCurr) ) ) ).

tff(writeUnaryOperator_8,axiom,
    ! [VarCurr: state_type] :
      ( ~ v293(VarCurr)
    <=> v160(VarCurr,1) ) ).

tff(addBitVectorEqualityBitBlasted_7,axiom,
    ! [VarCurr: state_type] :
      ( v282(VarCurr)
    <=> ( ( v283(VarCurr,1)
        <=> $false )
        & ( v283(VarCurr,0)
        <=> $true ) ) ) ).

tff(addAssignment_65,axiom,
    ! [VarCurr: state_type] :
      ( v283(VarCurr,0)
    <=> v264(VarCurr) ) ).

tff(addAssignment_64,axiom,
    ! [VarCurr: state_type] :
      ( v283(VarCurr,1)
    <=> v165(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_10,axiom,
    ! [VarCurr: state_type] :
      ( v264(VarCurr)
    <=> ( v156(VarCurr)
        | v266(VarCurr) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_3,axiom,
    ! [VarCurr: state_type] :
      ( ~ v268(VarCurr)
     => ( v266(VarCurr)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_3,axiom,
    ! [VarCurr: state_type] :
      ( v268(VarCurr)
     => ( v266(VarCurr)
      <=> v277(VarCurr) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1_1,axiom,
    ! [VarCurr: state_type] :
      ( ~ v270(VarCurr)
     => ( v277(VarCurr)
      <=> $false ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0_1,axiom,
    ! [VarCurr: state_type] :
      ( v270(VarCurr)
     => ( v277(VarCurr)
      <=> v278(VarCurr) ) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_2,axiom,
    ! [VarCurr: state_type] :
      ( ~ v158(VarCurr)
     => ( v278(VarCurr)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_2,axiom,
    ! [VarCurr: state_type] :
      ( v158(VarCurr)
     => ( v278(VarCurr)
      <=> $true ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_9,axiom,
    ! [VarCurr: state_type] :
      ( v268(VarCurr)
    <=> ( v269(VarCurr)
        & v274(VarCurr) ) ) ).

tff(writeUnaryOperator_7,axiom,
    ! [VarCurr: state_type] :
      ( ~ v274(VarCurr)
    <=> v275(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_8,axiom,
    ! [VarCurr: state_type] :
      ( v275(VarCurr)
    <=> ( v276(VarCurr)
        & v158(VarCurr) ) ) ).

tff(writeUnaryOperator_6,axiom,
    ! [VarCurr: state_type] :
      ( ~ v276(VarCurr)
    <=> v121(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_7,axiom,
    ! [VarCurr: state_type] :
      ( v269(VarCurr)
    <=> ( v270(VarCurr)
        | v273(VarCurr) ) ) ).

tff(writeUnaryOperator_5,axiom,
    ! [VarCurr: state_type] :
      ( ~ v273(VarCurr)
    <=> v272(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_6,axiom,
    ! [VarCurr: state_type] :
      ( v270(VarCurr)
    <=> ( v271(VarCurr)
        & v272(VarCurr) ) ) ).

tff(writeUnaryOperator_4,axiom,
    ! [VarCurr: state_type] :
      ( ~ v272(VarCurr)
    <=> v90(VarCurr) ) ).

tff(addBitVectorEqualityBitBlasted_6,axiom,
    ! [VarCurr: state_type] :
      ( v271(VarCurr)
    <=> ( ( v88(VarCurr,1)
        <=> $false )
        & ( v88(VarCurr,0)
        <=> $true ) ) ) ).

tff(bitBlastConstant_13,axiom,
    ~ b01(1) ).

tff(bitBlastConstant_12,axiom,
    b01(0) ).

tff(addAssignment_63,axiom,
    ! [VarCurr: state_type] :
      ( v165(VarCurr)
    <=> v167(VarCurr) ) ).

tff(addAssignment_62,axiom,
    ! [VarCurr: state_type] :
      ( v167(VarCurr)
    <=> v169(VarCurr) ) ).

tff(addAssignment_61,axiom,
    ! [VarCurr: state_type] :
      ( v169(VarCurr)
    <=> v171(VarCurr) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch_1,axiom,
    ! [VarCurr: state_type] :
      ( ~ v255(VarCurr)
     => ( v171(VarCurr)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch_1,axiom,
    ! [VarCurr: state_type] :
      ( v255(VarCurr)
     => ( v171(VarCurr)
      <=> v262(VarCurr) ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges1,axiom,
    ! [VarCurr: state_type] :
      ( ~ v256(VarCurr)
     => ( v262(VarCurr)
      <=> $false ) ) ).

tff(addParallelCaseBooleanConditionEqualRanges0,axiom,
    ! [VarCurr: state_type] :
      ( v256(VarCurr)
     => ( v262(VarCurr)
      <=> $true ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_5,axiom,
    ! [VarCurr: state_type] :
      ( v255(VarCurr)
    <=> ( v256(VarCurr)
        | v258(VarCurr) ) ) ).

tff(writeUnaryOperator_3,axiom,
    ! [VarCurr: state_type] :
      ( ~ v258(VarCurr)
    <=> v259(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_4,axiom,
    ! [VarCurr: state_type] :
      ( v259(VarCurr)
    <=> ( v260(VarCurr)
        | v256(VarCurr) ) ) ).

tff(addBitVectorEqualityBitBlasted_5,axiom,
    ! [VarCurr: state_type] :
      ( v260(VarCurr)
    <=> ( ( v261(VarCurr,2)
        <=> $false )
        & ( v261(VarCurr,1)
        <=> $false )
        & ( v261(VarCurr,0)
        <=> $true ) ) ) ).

tff(bitBlastConstant_11,axiom,
    ~ b001(2) ).

tff(bitBlastConstant_10,axiom,
    ~ b001(1) ).

tff(bitBlastConstant_9,axiom,
    b001(0) ).

tff(addAssignment_60,axiom,
    ! [VarCurr: state_type] :
      ( v261(VarCurr,0)
    <=> v236(VarCurr) ) ).

tff(addAssignment_59,axiom,
    ! [VarCurr: state_type] :
      ( v261(VarCurr,1)
    <=> v210(VarCurr) ) ).

tff(addAssignment_58,axiom,
    ! [VarCurr: state_type] :
      ( v261(VarCurr,2)
    <=> v173(VarCurr) ) ).

tff(addBitVectorEqualityBitBlasted_4,axiom,
    ! [VarCurr: state_type] :
      ( v256(VarCurr)
    <=> ( ( v257(VarCurr,2)
        <=> $false )
        & ( v257(VarCurr,1)
        <=> $true )
        & ( v257(VarCurr,0)
        <=> $false ) ) ) ).

tff(bitBlastConstant_8,axiom,
    ~ b010(2) ).

tff(bitBlastConstant_7,axiom,
    b010(1) ).

tff(bitBlastConstant_6,axiom,
    ~ b010(0) ).

tff(addAssignment_57,axiom,
    ! [VarCurr: state_type] :
      ( v257(VarCurr,0)
    <=> v236(VarCurr) ) ).

tff(addAssignment_56,axiom,
    ! [VarCurr: state_type] :
      ( v257(VarCurr,1)
    <=> v210(VarCurr) ) ).

tff(addAssignment_55,axiom,
    ! [VarCurr: state_type] :
      ( v257(VarCurr,2)
    <=> v173(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_3,axiom,
    ! [VarCurr: state_type] :
      ( v236(VarCurr)
    <=> ( v250(VarCurr)
        & v251(VarCurr) ) ) ).

tff(writeUnaryOperator_2,axiom,
    ! [VarCurr: state_type] :
      ( ~ v251(VarCurr)
    <=> v246(VarCurr) ) ).

tff(addBitVectorEqualityBitBlasted_3,axiom,
    ! [VarCurr: state_type] :
      ( v250(VarCurr)
    <=> ( ( v212(VarCurr,7)
        <=> v238(VarCurr,7) )
        & ( v212(VarCurr,6)
        <=> v238(VarCurr,6) )
        & ( v212(VarCurr,5)
        <=> v238(VarCurr,5) )
        & ( v212(VarCurr,4)
        <=> v238(VarCurr,4) )
        & ( v212(VarCurr,3)
        <=> v238(VarCurr,3) )
        & ( v212(VarCurr,2)
        <=> v238(VarCurr,2) )
        & ( v212(VarCurr,1)
        <=> v238(VarCurr,1) )
        & ( v212(VarCurr,0)
        <=> v238(VarCurr,0) ) ) ) ).

tff(addAssignment_54,axiom,
    ! [VarCurr: state_type] :
      ( v246(VarCurr)
    <=> v248(VarCurr) ) ).

tff(addAssignment_53,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,8)
        & ~ $less(B,0) )
     => ( v238(VarCurr,B)
      <=> v240(VarCurr,B) ) ) ).

tff(addAssignment_52,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,8)
        & ~ $less(B,0) )
     => ( v240(VarCurr,B)
      <=> v242(VarCurr,B) ) ) ).

tff(addAssignment_51,axiom,
    ! [VarCurr: state_type] :
      ( ( v242(VarCurr,7)
      <=> v244(VarCurr,400) )
      & ( v242(VarCurr,6)
      <=> v244(VarCurr,399) )
      & ( v242(VarCurr,5)
      <=> v244(VarCurr,398) )
      & ( v242(VarCurr,4)
      <=> v244(VarCurr,397) )
      & ( v242(VarCurr,3)
      <=> v244(VarCurr,396) )
      & ( v242(VarCurr,2)
      <=> v244(VarCurr,395) )
      & ( v242(VarCurr,1)
      <=> v244(VarCurr,394) )
      & ( v242(VarCurr,0)
      <=> v244(VarCurr,393) ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_2,axiom,
    ! [VarCurr: state_type] :
      ( v210(VarCurr)
    <=> ( v233(VarCurr)
        & v234(VarCurr) ) ) ).

tff(writeUnaryOperator_1,axiom,
    ! [VarCurr: state_type] :
      ( ~ v234(VarCurr)
    <=> v225(VarCurr) ) ).

tff(addBitVectorEqualityBitBlasted_2,axiom,
    ! [VarCurr: state_type] :
      ( v233(VarCurr)
    <=> ( ( v212(VarCurr,7)
        <=> v214(VarCurr,7) )
        & ( v212(VarCurr,6)
        <=> v214(VarCurr,6) )
        & ( v212(VarCurr,5)
        <=> v214(VarCurr,5) )
        & ( v212(VarCurr,4)
        <=> v214(VarCurr,4) )
        & ( v212(VarCurr,3)
        <=> v214(VarCurr,3) )
        & ( v212(VarCurr,2)
        <=> v214(VarCurr,2) )
        & ( v212(VarCurr,1)
        <=> v214(VarCurr,1) )
        & ( v212(VarCurr,0)
        <=> v214(VarCurr,0) ) ) ) ).

tff(addAssignment_50,axiom,
    ! [VarCurr: state_type] :
      ( v225(VarCurr)
    <=> v227(VarCurr) ) ).

tff(addBitVectorEqualityBitBlasted_1,axiom,
    ! [VarCurr: state_type] :
      ( v227(VarCurr)
    <=> ( ( v229(VarCurr,3)
        <=> $false )
        & ( v229(VarCurr,2)
        <=> $false )
        & ( v229(VarCurr,1)
        <=> $false )
        & ( v229(VarCurr,0)
        <=> $false ) ) ) ).

tff(bitBlastConstant_5,axiom,
    ~ b0000(3) ).

tff(bitBlastConstant_4,axiom,
    ~ b0000(2) ).

tff(bitBlastConstant_3,axiom,
    ~ b0000(1) ).

tff(bitBlastConstant_2,axiom,
    ~ b0000(0) ).

tff(addAssignment_49,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,8)
        & ~ $less(B,0) )
     => ( v214(VarCurr,B)
      <=> v216(VarCurr,B) ) ) ).

tff(addAssignment_48,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,8)
        & ~ $less(B,0) )
     => ( v216(VarCurr,B)
      <=> v218(VarCurr,B) ) ) ).

tff(addAssignment_47,axiom,
    ! [VarCurr: state_type,B: $int] :
      ( ( $less(B,8)
        & ~ $less(B,0) )
     => ( v218(VarCurr,B)
      <=> v223(VarCurr,B) ) ) ).

tff(addAssignment_46,axiom,
    ! [VarCurr: state_type] :
      ( v173(VarCurr)
    <=> v175(VarCurr) ) ).

tff(addAssignment_45,axiom,
    ! [VarCurr: state_type] :
      ( v175(VarCurr)
    <=> v177(VarCurr) ) ).

tff(addAssignment_44,axiom,
    ! [VarCurr: state_type] :
      ( v177(VarCurr)
    <=> v179(VarCurr) ) ).

tff(addAssignment_43,axiom,
    ! [VarCurr: state_type] :
      ( v179(VarCurr)
    <=> v181(VarCurr) ) ).

tff(addAssignment_42,axiom,
    ! [VarCurr: state_type] :
      ( v181(VarCurr)
    <=> v183(VarCurr) ) ).

tff(addAssignment_41,axiom,
    ! [VarCurr: state_type] :
      ( v183(VarCurr)
    <=> v185(VarCurr) ) ).

tff(addAssignment_40,axiom,
    ! [VarCurr: state_type] :
      ( v185(VarCurr)
    <=> v187(VarCurr) ) ).

tff(addAssignment_39,axiom,
    ! [VarCurr: state_type] :
      ( v187(VarCurr)
    <=> v189(VarCurr) ) ).

tff(addAssignment_38,axiom,
    ! [VarCurr: state_type] :
      ( v189(VarCurr)
    <=> v191(VarCurr) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits_1,axiom,
    ! [VarCurr: state_type] :
      ( v191(VarCurr)
    <=> ( v193(VarCurr)
        | v201(VarCurr) ) ) ).

tff(addAssignment_37,axiom,
    ! [VarCurr: state_type] :
      ( v201(VarCurr)
    <=> v203(VarCurr,6) ) ).

tff(addAssignment_36,axiom,
    ! [VarCurr: state_type] :
      ( v203(VarCurr,6)
    <=> v205(VarCurr,6) ) ).

tff(addAssignment_35,axiom,
    ! [VarCurr: state_type] :
      ( v205(VarCurr,6)
    <=> v207(VarCurr,6) ) ).

tff(addAssignment_34,axiom,
    ! [VarCurr: state_type] :
      ( v193(VarCurr)
    <=> v195(VarCurr,2) ) ).

tff(addAssignment_33,axiom,
    ! [VarCurr: state_type] :
      ( v195(VarCurr,2)
    <=> v197(VarCurr,2) ) ).

tff(addAssignment_32,axiom,
    ! [VarCurr: state_type] :
      ( v197(VarCurr,2)
    <=> v199(VarCurr,2) ) ).

tff(addAssignment_31,axiom,
    ! [VarCurr: state_type] :
      ( v132(VarCurr)
    <=> v134(VarCurr) ) ).

tff(addAssignment_30,axiom,
    ! [VarCurr: state_type] :
      ( v134(VarCurr)
    <=> v136(VarCurr) ) ).

tff(addAssignment_29,axiom,
    ! [VarCurr: state_type] :
      ( v136(VarCurr)
    <=> v138(VarCurr) ) ).

tff(addAssignment_28,axiom,
    ! [VarCurr: state_type] :
      ( v138(VarCurr)
    <=> v140(VarCurr) ) ).

tff(addAssignment_27,axiom,
    ! [VarCurr: state_type] :
      ( v140(VarCurr)
    <=> v142(VarCurr) ) ).

tff(addAssignment_26,axiom,
    ! [VarCurr: state_type] :
      ( v142(VarCurr)
    <=> v144(VarCurr) ) ).

tff(addAssignment_25,axiom,
    ! [VarCurr: state_type] :
      ( v144(VarCurr)
    <=> v146(VarCurr) ) ).

tff(addBitVectorEqualityBitBlasted,axiom,
    ! [VarCurr: state_type] :
      ( v146(VarCurr)
    <=> ( ( v148(VarCurr,1)
        <=> $true )
        & ( v148(VarCurr,0)
        <=> $true ) ) ) ).

tff(bitBlastConstant_1,axiom,
    b11(1) ).

tff(bitBlastConstant,axiom,
    b11(0) ).

tff(addAssignment_24,axiom,
    ! [VarCurr: state_type] :
      ( v127(VarCurr)
    <=> v82(VarCurr) ) ).

tff(addAssignment_23,axiom,
    ! [VarCurr: state_type] :
      ( v96(VarCurr)
    <=> v98(VarCurr) ) ).

tff(addAssignment_22,axiom,
    ! [VarCurr: state_type] :
      ( v98(VarCurr)
    <=> v100(VarCurr) ) ).

tff(addAssignment_21,axiom,
    ! [VarCurr: state_type] :
      ( v100(VarCurr)
    <=> v102(VarCurr) ) ).

tff(addAssignment_20,axiom,
    ! [VarCurr: state_type] :
      ( v102(VarCurr)
    <=> v104(VarCurr) ) ).

tff(addAssignment_19,axiom,
    ! [VarCurr: state_type] :
      ( v104(VarCurr)
    <=> v106(VarCurr) ) ).

tff(addAssignment_18,axiom,
    ! [VarCurr: state_type] :
      ( v106(VarCurr)
    <=> v108(VarCurr) ) ).

tff(addAssignment_17,axiom,
    ! [VarCurr: state_type] :
      ( v108(VarCurr)
    <=> v110(VarCurr) ) ).

tff(addAssignment_16,axiom,
    ! [VarCurr: state_type] :
      ( v110(VarCurr)
    <=> v112(VarCurr,1) ) ).

tff(addAssignment_15,axiom,
    ! [VarCurr: state_type] :
      ( v94(VarCurr)
    <=> v82(VarCurr) ) ).

tff(addAssignment_14,axiom,
    ! [VarCurr: state_type] :
      ( v82(VarCurr)
    <=> v84(VarCurr) ) ).

tff(addAssignment_13,axiom,
    ! [VarCurr: state_type] :
      ( v84(VarCurr)
    <=> v12(VarCurr) ) ).

tff(addAssignment_12,axiom,
    ! [VarCurr: state_type] :
      ( v66(VarCurr)
    <=> v8(VarCurr) ) ).

tff(addAssignment_11,axiom,
    ! [VarCurr: state_type] :
      ( v32(VarCurr)
    <=> v34(VarCurr) ) ).

tff(aaddConditionBooleanCondEqualRangesElseBranch,axiom,
    ! [VarCurr: state_type] :
      ( ~ v53(VarCurr)
     => ( v34(VarCurr)
      <=> $false ) ) ).

tff(addConditionBooleanCondEqualRangesThenBranch,axiom,
    ! [VarCurr: state_type] :
      ( v53(VarCurr)
     => ( v34(VarCurr)
      <=> $true ) ) ).

tff(writeBinaryOperatorEqualRangesSingleBits,axiom,
    ! [VarCurr: state_type] :
      ( v53(VarCurr)
    <=> ( v54(VarCurr)
        & v44(VarCurr) ) ) ).

tff(writeUnaryOperator,axiom,
    ! [VarCurr: state_type] :
      ( ~ v54(VarCurr)
    <=> v36(VarCurr,8) ) ).

tff(addAssignment_10,axiom,
    ! [VarCurr: state_type] :
      ( v44(VarCurr)
    <=> v46(VarCurr) ) ).

tff(addAssignment_9,axiom,
    ! [VarCurr: state_type] :
      ( v46(VarCurr)
    <=> v48(VarCurr) ) ).

tff(addAssignment_8,axiom,
    ! [VarCurr: state_type] :
      ( v48(VarCurr)
    <=> v50(VarCurr) ) ).

tff(addAssignment_7,axiom,
    ! [VarCurr: state_type] :
      ( v36(VarCurr,8)
    <=> v38(VarCurr,8) ) ).

tff(addAssignment_6,axiom,
    ! [VarCurr: state_type] :
      ( v38(VarCurr,8)
    <=> v40(VarCurr,8) ) ).

tff(addAssignment_5,axiom,
    ! [VarCurr: state_type] :
      ( v40(VarCurr,8)
    <=> v42(VarCurr,8) ) ).

tff(addAssignment_4,axiom,
    ! [VarCurr: state_type] :
      ( v27(VarCurr)
    <=> v8(VarCurr) ) ).

tff(addAssignment_3,axiom,
    ! [VarCurr: state_type] :
      ( v8(VarCurr)
    <=> v10(VarCurr) ) ).

tff(addAssignment_2,axiom,
    ! [VarCurr: state_type] :
      ( v10(VarCurr)
    <=> v12(VarCurr) ) ).

tff(addAssignment_1,axiom,
    ! [VarCurr: state_type] :
      ( v12(VarCurr)
    <=> v14(VarCurr) ) ).

tff(addAssignment,axiom,
    ! [VarCurr: state_type] :
      ( v14(VarCurr)
    <=> v16(VarCurr) ) ).

%------------------------------------------------------------------------------
