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

  $content =~ s/(\A|[^\/])\/\*.*?\*\///gs;
  $content =~ s/\/\/[^\n]*//gs;
  $content =~ s/\/\/[^\n]*//gs;
  my $CASC = 'CASC-J6';

  open OUT, ">$file" or die "cannot open $file: $!";
  my $trunc = $file;
  $trunc =~ s/\A.*\///g;
  print OUT qq{
/*
 * File $trunc.
 *
 * This file is part of the source code of the software program
 * Vampire as used in $CASC. It is protected by applicable
 * copyright laws.
 *
 * Posession of, or access to, this program does not
 * give you or anybody else a right or licence to
 * distribute, modify, copy, compile, create derivatives,
 * or use in any form or for any purpose, this program,
 * or any part thereof.
 * Any licence to use Vampire shall only be obtained
 * as described on Vampire's home page http://www.vprover.org.
 *
 * This file was included in the Vampire source code
 * for $CASC only because so is required by the $CASC
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

