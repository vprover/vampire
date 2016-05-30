#!/usr/bin/perl -w

use strict;

# AV: this is a very simple stcipt for making fallback strategies for SMT-COMP

my $file =  "SMTCOMP/SMTCOMPMode.cpp";

sub createFallback {
  open IN, "<$file" or die;

  my %strat;
  while (my $line = <IN>) {
    next if $line !~ /quick\.push\("(.*)_(\d+)"\);/;
    my ($strat,$time) = ($1,$2);
    next if $strat =~ /\Afmb/;
    $strat =~ s/stl=\d+://;
    $strat{$strat} = rand();
  }
  close IN;
  map {print "      fallback.push(\"$_\_3000\");\n"}
    sort {$strat{$a} <=> $strat{$b}}
    keys %strat;
} # createFallback

createFallback();


