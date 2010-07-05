#!/usr/bin/perl -w

use strict;
use File::Find;

my $tmpfile = "tmp";

# to read the whole file at once
undef $/;

sub uncomment {
  my $file = $File::Find::name;
  if ($file !~ m/(c|h)pp\z/) {
    return;
  }
  print "$file\n";
  open FILE, "<$file" or die "cannot open $file: $!";
  my $content = <FILE>;
  close FILE;

  $content =~ s/\/\*.*?\*\///gs;
  $content =~ s/\/\/[^\n]*//gs;

  open OUT, ">$file" or die "cannot open $file: $!";
  print OUT qq{
/*
 * File $file.
 *
 * This file is part of the source code of the software program
 * Vampire as used in CASC-J5. It is protected by applicable
 * copyright laws.
 *
 * Posession of, or access to, this program does not
 * give you or anybody else a right or licence to
 * distribute, modify, create derivatives
 * or use in any form, this program or any part thereof.
 * Any licence to use Vampire shall only be obtained
 * as described on Vampire's home page http://www.vprover.org.
 *
 * This file has been included in the Vampire source code
 * for CASC-J5 only because so is required by the CASC-J5
 * rules, and for no other reason.
 */
}, $content;

  close OUT;
} # sub uncomment

sub uncommentAll {
  my $dir = $ARGV[0];
  die if ! $dir;
  find(\&uncomment,$dir);
}

uncommentAll();


