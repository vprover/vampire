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
 * @file DHMap.cpp
 *
 */

#include "DHMap.hpp"

namespace Lib {

const unsigned DHMapTableCapacities[]={
    0,
    7,
    13,
    31,
    61,
    127,
    251,
    509,
    1021,
    2039,
    4093,
    8191,
    16381,
    32749,
    65521,
    131071,
    262139,
    524287,
    1048573,
    2097143,
    4194301,
    8388593,
    16777213,
    33554393,
    67108859,
    134217689,
    268435399,
    536870909,
    1073741789,
    2147483647,
};

//next expansion occupancy is equal to 0.7*capacity
const unsigned DHMapTableNextExpansions[]={
    0,
    4,
    9,
    21,
    42,
    88,
    175,
    356,
    714,
    1427,
    2865,
    5733,
    11466,
    22924,
    45864,
    91749,
    183497,
    367000,
    734001,
    1468000,
    2936010,
    5872015,
    11744049,
    23488075,
    46976201,
    93952382,
    187904779,
    375809636,
    751619252,
    1503238552,

};

};
