#!/usr/bin/perl
####################################################################################################################################
# Cisco IP Phone Inventory Tool (CIPIT)
# This Script was originally written by Vince Loschiavo on 2012-JAN-03 Original project: https://sourceforge.net/projects/cipinventory/
#
# New branch author: Michael Randolph on 2016-OCT-13
#
# if you enjoy it or have comments/suggestions
#   email: <first name> + <c> + <last name> @ gmail d0t com
# 
# Follow new project branch on GitHub
# New project branch: https://github.com/michaelcrandolph/Cisco-IP-Phone-Inventory-Tool
#
# This script was tested with Cisco SCCP images:
# CP-6921G
# CP-7905G / CP-7906G
# CP-7910G / CP-7911G / CP-7912G / CP-7920 / CP-7921G / CP-7925G / CP-7925G-E
# CP-7935 - Tested and Not working
# CP-7936 - Tested and Not working
# CP-7937G / CP-7940G / CP-7941G / CP-7942G / CP-7945G
# CP-7960G / CP-7961G / CP-7962G / CP-7965G / CP-7970G / CP-7971G-G / CP-7975G / CP-7985G
# CP-9951 / CP-9971
#
# When Reading from a File of IP Addresses:
#	-Includes Duplicate IP checking
#	-Reporting on Phones not responding
#
# General:
#	-Now parses phone XML for greater portability across localizations.
#		Tested on: English, French, and Chinese localizations
#	-Overwrite file check
#	-progress indicator to let you know it's actually doing something
#	-Calculate execution time
# 	-CIDR IP Address Entry from Commandline
#	-Improved overall speed
#		-By using:
#		   -TCP/Syn-ACK Echo to test IP Reachability
#		   -IO::Socket::INET to test if TCP port 80/443 is open
#	-IP Addresses sorted in output file
#	-Included warning for CIDR less than /23 as this can
#		put a lot of load on your network.
#	-Verbose Option to see the action
#	-Better (-h --help) help options and output
#	-Commandline option for multiple iterations through the SYN/ACK discovery process for greater accuracy
#	-Added support for HTTPS
#
####################################################################################################################################

#####################################
#  Define Variables & Includes		#
#####################################

use LWP::Simple;
use LWP::UserAgent;
use Net::Ping;
use Time::HiRes;
use IO::Socket::INET;
use Sort::Key::IPv4 qw(ipv4sort);
use NetAddr::IP;
use Getopt::Long;
use Pod::Usage;
use XML::Simple;

use strict;
use warnings;

my $now = time; 		# - This variable holds the current time and will be used to calculate the total script runtime.
my @sparkle = qw( \ | / - );	# Other Progress indicator characters;
# my @sparkle = qw( ^ > v < );  # Other Progress indicator characters;
# my @sparkle = ("(", "]", ")", "|", "(", "|", ")", ")");  # Other Progress indicator characters;
# my @sparkle = qw( . o O o );  # This is the progress indicator characters array;

my $cur_sparkle = 0;		# Progress indicator counter
my $url;					# This is the url of the phone's web page
my $xml_url;
my $PhoneRecordNumber = 0;	# This will be used as a unique record number
my $PhoneIPs;				# This is the number of valid IP addresses found in file
my $content;				# This contains the phone web page
my %IPlist = ();			# This is a hash to store unique IP addresses
my %IPs = ();				# This is a hash to store unique IP addresses
my $CurrentHost;
my $versionnumber = ("0.11");	# This script's version number
$| = 1;				# Autoflush-This is to avoid buffering output to STDOUT or FILEHANDLES
my @cidr;			# Array of IP ranges in CIDR format.
my $cidr;			# Individual IP Range in CIDR Format for parsing
my $host;			# Individual Host IP
my @cidr_host_array;	# Array ip IP addresses from all CIDR ranges
my @PhoneIPs;			# Scrubbed Array of IPs that 1. Are alive, 2. Have TCP port 80 open.
my $count;

# Define Commandline Variables
my $opt_inputfile = undef;		# input filename
my $opt_outputfile = "output.csv";	# output filename
my @opt_I;				# IP Addresses or IP/CIDR entries
my $opt_v = undef;		# verbose
my $opt_f = undef;		# force file overwrite (don't ask to overwrite file)
my $opt_h = undef;		# Usage Help
my $opt_timeout = 8;	# Ping and IO::Socket timeout - Default set at 8 seconds as some phones take a looong time to respond to TCP syn & IO:Socket requests
my $opt_repeat = 2;		# Number of times through the SYN/ACK/Socket loop (Default = 2);
my $xml_switchinfo_url;	# URL for switch port info
my $content_net;		# Switch port XML data

Getopt::Long::Configure("no_ignore_case");
GetOptions(
                'inputfile:s'	=> \$opt_inputfile,
                'outputfile=s'	=> \$opt_outputfile,
                'IP:s{,}'		=> \@opt_I,
				'timeout:i'		=> \$opt_timeout,
                'verbose'		=> \$opt_v,
                'force'			=> \$opt_f,
                'help!'			=> \$opt_h,
				'repeat:i'		=> \$opt_repeat,
                ) or pod2usage(-verbose => 1) && exit;

pod2usage(-verbose => 2) && exit if defined $opt_h;

if (defined $opt_inputfile && exists $opt_I[0]) {
        print STDERR "\n$0: Cannot specify hosts from both commandline -I and hostsfile -i\n\n";
        sleep (2);
        pod2usage(-verbose => 1);
        print "\n";
        exit(1);
}

# If inputfile or IPs were not specified, then display help and exit.
pod2usage(-verbose => 1) unless defined ($opt_inputfile || $opt_I[0]);

# Check to see if there's a .CSV extension on the end of the outputfile name
if ($opt_outputfile !~ /\.csv$/i) {
	$opt_outputfile = ($opt_outputfile . ".csv");	# Add .csv extenstion if it's missing.
}

unless ($opt_f) {
	if (-e $opt_outputfile) {
		print ("\n\nWarning!\n\nThe file: $opt_outputfile already exists.\nWould you like to replace? ");
		if (<STDIN> !~ /^[Yy]/) {
			exit;
		 }
	}
}

# If -I or --IP is specified, then parse the IP or IP/CIDR input and store values in @cidr
if ($opt_I[0]) {
	foreach $_ (@opt_I) {
		if ($_ =~  /\b(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\b/) {
			push (@cidr,$_);
			if (($_ =~ /\/([0-9]{1,2})\z/) && ($1 <=22)) {
				print "\n\nWarning: IP mask of /22 or lower is not recommended due to high traffic generation especially over slow WAN links.\nPlease be kind to your users.\nHit <CTRL-C> to stop\n";
			}
		} else {
			print "\nError: not a valid IP or IP/CIDR.\n";
		}
	}
	&CIDR_to_IPs();
}

if ($opt_inputfile) {
	&Parse_InputFile();
}

# Create the $opt_outputfile and begin checking content, open a file for writing
open (CSVOUTPUT, "> $opt_outputfile") or die "Couldn't open $opt_outputfile for writing: $!\n";

# Write CSV File Header
print CSVOUTPUT ("Phone Record Number,IP Address,Model Number,MAC Address,Host Name,Phone DN,Phone Load Version,Phone Serial Number,XML Capable,CDP Switch Host Name,CDP Switch IPv4 Address,CDP Switch IPv6 Address,CDP Switch Port,LLDP Switch Hostname,LLDP Switch IPv4 Address,LLDP Switch IPv6 Address,LLDP Switch Port,Port Speed,Port Duplex,Port Information\n");
print("Parsing Web Pages: ");
print(' ');
# get the xml or html for each IP

BIG:	foreach (@PhoneIPs) {
		$cur_sparkle = ($cur_sparkle + 1) % @sparkle;
		print("\010$sparkle[$cur_sparkle]");
		#$xml_url = "http://$_" . '/' . "DeviceInformationX";				# HTTP XML url for Main Device Information Page
		$xml_url = "https://$_" . '/' . "DeviceInformationX";			    # HTTPS XML url for Main Device Information Page
		
		# $content = get $xml_url; # HTTP method
        my $ua = LWP::UserAgent->new;                                       # HTTPS
        my $req = HTTP::Request->new(GET => $xml_url);                      # HTTPS
        my $res = $ua->request($req);                                       # HTTPS
		
        #if ($res->is_success) {
        #    print $res->content;
        #}
        #else {
        #    print "Failed: ", $content->status_line, "\n";
        #}
		$content = $res->content;
		
		# $xml_switchinfo_url = "http://$_" . '/CGI/Java/Serviceability?adapterX=device.statistics.port.network';	# HTTP XML page for Network Port information
		$xml_switchinfo_url = "https://$_" . '/CGI/Java/Serviceability?adapterX=device.statistics.port.network';	# HTTPS XML page for Network Port information
		# $content_net = get $xml_switchinfo_url; # HTTP method
        $req = HTTP::Request->new(GET => $xml_switchinfo_url);       # HTTPS
        $res = $ua->request($req);                                   # HTTPS
		$content_net = $res->content;                                # HTTPS
		
		# Sanity check for grabbed phone-web page content
		if (not defined($content)) {										# Phone doesn't support XML - handle the phone web page as best as possible
			# $url = "http://$_";  											# HTTP: Phone Does not support XML.  Let's grab the default page.
			$url = "https://$_";  											# HTTPS: Phone Does not support XML.  Let's grab the default page.
		    # $content = get $url;											# HTTP
		    $req = HTTP::Request->new(GET => $xml_switchinfo_url);          # HTTPS
            $res = $ua->request($req);                                      # HTTPS
		    $content = $res->content;			                            # HTTPS
		}
		if (not defined($content)) { 										# Check if $content is defined and from a phone.
			next BIG;
		} elsif ($content !~ (/xml version|IP Phone|dynaform/i)) {
			next BIG;
		}
		# Sanity check for grabbed Serviceability page
		if (not defined($content_net)) {											# Phone may be a CP-7960 which has a different URL structure for the Serviceability page
			$xml_switchinfo_url = "http://$_" . '/PortInformationX?1';				# XML URL for the older CP-7960 (and CP-7940s?)
			$content_net = get $xml_switchinfo_url;
		}

		$PhoneRecordNumber++;           # Increment the Record Number Counter

		# Let's look for the information we need.
		print CSVOUTPUT "$PhoneRecordNumber,";	# Print the Record Number
		print CSVOUTPUT "$_,";			# Print the IP Address of the Phone

		# Check model numbers - if the xml content doesn't exist, try handling the content from the default web pages
		# http get and grep for the content (not as reliable as the XML format as the phone web pages can change 
		# firmware version
		if($content =~ /xml version/) {		# parse XML $content - Most phones should be parsed here.
			&parse_xml($content);
		} elsif($content =~ /ATA 18/) {		#if it's an ATA186 or ATA188 then call the 18x subroutine
			&ata18x($content, $url);
		# } elsif ($content =~ /CP-7920/) {	# if it's a 7920...call that sub
		} elsif ($content =~ /CP-7925G/) {	# if it's a 7920...call that sub
		 	&cp7920($content, $url);
		} elsif ($content =~ /dynaform\/index_Dyna.htm/) {	# if it's a 793x...call that sub
		 	&cp793x($content, $url);
		} elsif (($content =~ /CP-7911/) || ($content =~ /CP-7906G/)) {	# If it's a 7911 or 7906,  call that sub
			&cp7911($content, $url);
		} elsif (($content =~ /CP-7905G/) || ($content =~ /CP-7912G/)) {	# If it's a 7905 or a 7912, call that sub
		 	&cp79057912($content, $url);
		} elsif (($content =~ /CP-7985/)) {	# If it's a 7985, call that sub
		 	&cp7985($content, $url);
		} else {				# if it's none of the above, then do your best.

			# Most other phones:  Tested on 7910, 7941, 7960, 7961, 7970.
			if($content =~ /Model Number<\/B><\/TD>\W?<td width=20><\/TD>\W?<TD><B>([\+\/0-9A-Za-z-]+)<\/B><\/TD>/)
			 {
				print CSVOUTPUT ("$1,");
				} else {
				print CSVOUTPUT ("N/A,");
			 }

			# Find the MAC Address
			if($content =~ /MAC Address<\/B><\/TD>\W?<td width=20><\/TD>\W?<TD><B>([0-9A-Za-z-]+)<\/B><\/TD>/)
			 {
			        print CSVOUTPUT ("$1,");
			        } else {
	        		print CSVOUTPUT ("N/A,");
		 	}

			# Find the Host Name
			if($content =~ /Host Name<\/B><\/TD>\W?<td width=20><\/TD>\W?<TD><B>([0-9A-Za-z]+)<\/B><\/TD>/)
			 {
			        print CSVOUTPUT ("$1,");
			        } else {
			        print CSVOUTPUT ("N/A,");
			 }

			# Find the Phone's DN
			if($content =~ /Phone DN<\/B><\/TD>\W?<td width=20><\/TD>\W?<TD><B>([\+A-Da-d0-9]+)<\/B><\/TD>/)
			 {
			        print CSVOUTPUT ("$1,");
			        } else {
	        		print CSVOUTPUT ("N/A,");
			 }

			# Find the Phone Load Version number
			if($content =~ /Version<\/B><\/TD>\W?<td width=20><\/TD>\W?<TD><B>([\.\(\)0-9A-Za-z-]+)<\/B><\/TD>/)
			 {
		        	print CSVOUTPUT ("$1,");
			        } else {
		        	print CSVOUTPUT ("N/A,");
			 }

			# Find the Phone Serial Number
			if($content =~ /Serial Number<\/B><\/TD>\W?<td width=20><\/TD>\W?<TD><B>([0-9A-Za-z]+)<\/B><\/TD>/)
			 {
			        print CSVOUTPUT ("$1,");
			        } else {
			        print CSVOUTPUT ("N/A,");
			 }
			# Print a newline to start a new record
			print CSVOUTPUT ("false\n");
		 }	# end elseifs
		}	# foreach loop end

	close (CSVOUTPUT) || die "Can't close $opt_outputfile" + ": $!";	# Close File
print("\010 done.\n");   # or: print("\010 \010");			# Print 'done' on progress bar.

# Calculate the total script runtime
$now = time - $now; # - Calculate the total runtime (current time minus start time)
printf("\n\nTotal running time: %02d:%02d:%02d\n\n", int($now / 3600), int(($now % 3600) / 60), int($now % 60));
exit(0);

#################################
#
#	Begin Subroutines	   		
#				   				
#################################


sub Parse_InputFile {
	open (INPUTFILE, $opt_inputfile) || die "Couldn't open $opt_inputfile for reading:  $!\n";

	# First we will read each line of the file and look for a valid IP address, then add it to a hash as the Key, and increment the value.
	# This step removes any duplicate IPs.
	while (<INPUTFILE>) {
        	chomp;
	        if ($_ =~ /\b(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\b/) { 		# Verify that it's a valid IP address
		$CurrentHost = ("$1.$2.$3.$4");
	        $IPlist{$CurrentHost}++;		# Add item to Hash and increment value once
	        }
	}
	close INPUTFILE || die "Couldn't close $opt_inputfile for some reason: $!\n";

	# Let's do some sanity checking to verify the input file actually contains data.
	if (keys(%IPlist) > 0) {
 		# Print that number before we begin gathering data.
		print "\nI read $opt_inputfile sucessfully.\nThere are " . keys(%IPs) . " Valid IP Addresses.\n\n";
		# Test if IPs are alive
		@cidr = keys(%IPlist);
		&CIDR_to_IPs();
		
		# Print # of live hosts
		print "\nThere are " . keys(%IPs) . " Live IP Addresses.\n\n";
		
		@PhoneIPs = keys(%IPs);					#This puts the IPs into an array for ease of handling.
		@PhoneIPs = ipv4sort @PhoneIPs;
	} else {
		print "\n\nError: expecting a file that contains one IP address per line.\n";
		exit;
	}
}

#
# sub CIDR_to_IPs() - create an array of host addresses to test
#
sub CIDR_to_IPs {
	if ($opt_v) {
		print "SYN/ACK Timeout set at: $opt_timeout seconds.\n";
	}
	print ("\n    Finding alive hosts: ");
	print(' ');
	foreach $cidr (@cidr) {
		my $n = NetAddr::IP->new($cidr);
		push (@cidr_host_array , @{$n->hostenumref});
	}
	my $p = new Net::Ping "syn";
	# $p->{port_num} = getservbyname("http", "tcp");
	$p->{port_num} = getservbyname("https", "tcp");

	# Repeat multiple times based on commandline
	for ($count = $opt_repeat; $count >= 1; $count--) {

		# Ping the hosts
		foreach $host (@cidr_host_array) {
				$host =~ s/\/[0-9]+\z//; # Remove the "/32" from the end of the host string
				my ($ret,$nslookup_duration,$ip) = $p->ping($host,$opt_timeout);	# Ping the Host

			# Verbose option
			if ($ret) {
				if ($opt_v) {
					print"Pinging: $host\n";
				}
			}
		}

		# Verbose option
		if ($opt_v) { print "waiting for ack.\n";}

		# Listen to the ACKs
		while (my ($host,$rtt,$ip) = $p->ack) {
			$cur_sparkle = ($cur_sparkle + 1) % @sparkle unless $opt_v;
					print("\010$sparkle[$cur_sparkle]") unless $opt_v;
					if ($opt_v) {
						print "ACK: $host\n";
					}
			# Verify the TCP 80 is actually open
			if (IO::Socket::INET->new(PeerAddr=>$host,PeerPort=>443,proto=>'tcp',Timeout=>$opt_timeout)) {
				# Normally just be quite and add output to CSV
				if ($opt_v) {
					print "Ack:(" , $host , ":443) is open.\n\n";
				}
			}
			# Store the hosts in the %IPs hash with the IP as the key to remove duplicates
			$IPs{$host}++;
		}
		unless ($count > 1) {
			print("\010done.\n") unless $opt_v;   # or: print("\010 \010");			# Print done on progress bar.
		}
	} # end of the For Loop

	# Store the IPs into the @PhoneIPs array
	@PhoneIPs = keys(%IPs);
	# Sort the IPs
	@PhoneIPs = ipv4sort @PhoneIPs;
	$count = scalar(@PhoneIPs);	# Count the number of IPs
	if ($opt_v) {
		print ("\n\nHosts ACKed and Socket open:\n");
		foreach (@PhoneIPs) {print $_, "\n";}
	}
	print "            Total hosts: $count\n";
}

sub ata18x {
	# Check for Special Case: ATA186 and ATA188
 	$url = ($url . "/DeviceInfo");		# Change URL to get correct URL for this device
	$content = get $url;			# Get new URL

	# Get Product ID from Device
	if($content =~ /Product ID<\/td><td>([A-Za-z0-9]+)<\/td>/)
	 {
	 	print CSVOUTPUT ("$1,");
	 } else {
	 	print CSVOUTPUT ("N/A,");
	 }

	# Get MAC Address from Device
        if($content =~ /MAC Address<\/td><td>([A-Za-z0-9]+)<\/td>/)
         {
                print CSVOUTPUT ("$1,");
         } else {
                print CSVOUTPUT ("N/A,");
         }

	# Get Host Name from Device
        if($content =~ /Host Name<\/td><td>([A-Za-z0-9]+)<\/td>/)
         {
                print CSVOUTPUT ("$1,");
         } else {
                print CSVOUTPUT ("N/A,");
         }

	# Get Phone DN Port1 from Device
        if($content =~ /Phone 1 DN<\/td><td>([\+A-Da-d0-9]+)<\/td>/)
         {
                print CSVOUTPUT ("$1 ");
         } else {
                print CSVOUTPUT ("N/A ");
         }

	# Get Phone DN Port2 from Device
        if($content =~ /Phone 2 DN<\/td><td>([\+A-Da-d0-9]+)<\/td>/)
        {
                print CSVOUTPUT ("$1,");
         } else {
                print CSVOUTPUT ("N/A,");
         }

        # Get Firmware Load Version from Device
	if($content =~ /App Load ID<\/td><td>([A-Za-z0-9\.\-\_]+)<\/td>/)
         {
                print CSVOUTPUT ("$1,");
         } else {
                print CSVOUTPUT ("N/A,");
         }

	# Get Serial Number from Device
        if($content =~ /Serial Number<\/td><td>([A-Za-z0-9]+)<\/td>/)
         {
                print CSVOUTPUT ("$1,");
         } else {
                print CSVOUTPUT ("N/A,");
         }

	#Print a newline to start a new record
        print CSVOUTPUT ("false\n");
} # End Sub ata18x

sub cp7920 {
	# Check for Special Case: 7920 Wireless phone
	print CSVOUTPUT ("CP-7920,");	#Print Model Number

	# Find the MAC Address
	if($content =~ /<p><b>([A-Za-z0-9]+)<\/b><\/p><\/td><\/tr><tr style='irow:1'>/)
	 {
		print CSVOUTPUT ("$1,");
		} else {
	       	print CSVOUTPUT ("N/A,");
	}

	# Find the Host Name
	if($content =~ /<p><b>([A-Za-z0-9]+)<\/b><\/p><\/td><\/tr><tr style='irow:2'>/)
	 {
	        print CSVOUTPUT ("$1,");
	        } else {
	        print CSVOUTPUT ("N/A,");
	 }
	# Find the Phone's DN
	if($content =~ /<p><b>([\+A-Za-z0-9]+)<\/b><\/p><\/td><\/tr><tr style='irow:3'>/)
	 {
	        print CSVOUTPUT ("$1,");
	        } else {
		print CSVOUTPUT ("N/A,");
	 }

	# Find the Phone Load Version number
	if($content =~ /<p><b>([A-Za-z0-9\.-]+)<\/b><\/p><\/td><\/tr><tr style='irow:4'>/)
	 {
        	print CSVOUTPUT ("$1,");
	        } else {
        	print CSVOUTPUT ("N/A,");
	 }

	# Find the Phone Serial Number
if($content =~ /><b>([A-Za-z0-9]+)<\/b><\/p><\/td><\/tr><tr style='irow:9'>/)
	 {
	        print CSVOUTPUT ("$1,");
	        } else {
	        print CSVOUTPUT ("N/A,");
	 }
	#Print a newline to start a new record
	print CSVOUTPUT ("false\n");
}

#
# sub cp793x - Check for Special Case: 7935/7936 Conference Phone
#
sub cp793x {
	#
	$url = ($url . "/dynaform/index_Dyna.htm");		# Change URL to get correct URL for this device
	$content = get $url;					# Get new URL
	if ($content =~ /(79[0-9][0-9]) Cisco IP/) {
		print CSVOUTPUT ("CP-" . $1 . "G,");
	 } else {
	 	print CSVOUTPUT ("N/A,");
	 }
	print CSVOUTPUT ("N/A,");	#Print MAC Address
	print CSVOUTPUT ("N/A,");	#Print Host Name
	print CSVOUTPUT ("N/A,");	#Print Phone DN
	print CSVOUTPUT ("N/A,");	#Print Phone Load Version
	print CSVOUTPUT ("N/A,");	#Print Phone Serial Number
	print CSVOUTPUT ("false\n");		#Print a newline to start a new record
}

#
# sub cp711 - Check for Special Case
#
sub cp7911 {
	if($content =~ /Model Number<\/B><\/TD>\W?<td width=20><\/TD>\W?<TD><B>([\+\/0-9A-Za-z-]+)<\/B><\/TD>/)
	 {
		print CSVOUTPUT ("$1,");
		} else {
		print CSVOUTPUT ("N/A,");
	 }

	# Find the MAC Address
	if($content =~ /MAC Address<\/B><\/TD>\W?<td width=20><\/TD>\W?<TD><B>([0-9A-Za-z-]+)<\/B><\/TD>/)
	 {
	        print CSVOUTPUT ("$1,");
	        } else {
       		print CSVOUTPUT ("N/A,");
 	}

	# Find the Host Name
	if($content =~ /Host Name<\/B><\/TD>\W?<td width=20><\/TD>\W?<TD><B>([0-9A-Za-z]+)<\/B><\/TD>/)
	 {
	        print CSVOUTPUT ("$1,");
	        } else {
	        print CSVOUTPUT ("N/A,");
	 }

	# Find the Phone's DN
	if($content =~ /Phone DN<\/B><\/TD>\W?<td width=20><\/TD>\W?<TD><B>([\+0-9A-Za-z-]+)<\/B><\/TD>/)
	 {
	        print CSVOUTPUT ("$1,");
	        } else {
       		print CSVOUTPUT ("N/A,");
	 }

	# Find the Phone Load Version number
	if($content =~ /App Load ID<\/B><\/TD><td width=20><\/TD><TD><B>([A-Za-z0-9\.\-\_]+)<\/B><\/TD>/)
	 {
        	print CSVOUTPUT ("$1,");
	        } else {
        	print CSVOUTPUT ("N/A,");
	 }

	# Find the Phone Serial Number
	if($content =~ /Serial Number<\/B><\/TD>\W?<td width=20><\/TD>\W?<TD><B>([0-9A-Za-z]+)<\/B><\/TD>/)
	 {
	        print CSVOUTPUT ("$1,");
	        } else {
	        print CSVOUTPUT ("N/A,");
	 }
	# Print a newline to start a new record
	print CSVOUTPUT ("false\n");
}

#
# sub cp79057912 - Check for Special Case
#
sub cp79057912 {
	if($content =~ /Product ID<\/td><td>([\+\/0-9A-Za-z-]+)/)
	 {
		print CSVOUTPUT ("$1,");
		} else {
		print CSVOUTPUT ("N/A,");
	 }

	# Find the MAC Address
	if($content =~ /MAC Address<\/td><td>([A-Fa-f0-9]+)/)
	 {
	        print CSVOUTPUT ("$1,");
	        } else {
       		print CSVOUTPUT ("N/A,");
 	}

	# Find the Host Name
	if($content =~ /Host Name<\/td><td>([A-Za-z0-9]+)/)
	 {
	        print CSVOUTPUT ("$1,");
	        } else {
	        print CSVOUTPUT ("N/A,");
	 }

	# Find the Phone's DN
	if($content =~ /Phone DN<\/td><td>([\+A-Da-d0-9]+)/)
	 {
	        print CSVOUTPUT ("$1,");
	        } else {
       		print CSVOUTPUT ("N/A,");
	 }

	# Find the Phone Load Version number
	if($content =~ /Software Version<\/td><td>([\(\)A-Za-z0-9\.-]+)/)
	 {
        	print CSVOUTPUT ("$1,");
	        } else {
        	print CSVOUTPUT ("N/A,");
	 }

	# Find the Phone Serial Number
	if($content =~ /Serial Number<\/td><td>([0-9A-Za-z]+)/)
	 {
	        print CSVOUTPUT ("$1,");
	        } else {
	        print CSVOUTPUT ("N/A,");
	 }
	# Print a newline to start a new record
	print CSVOUTPUT ("false\n");
}

#
# sub cp7985 - Check for Special Case
#
sub cp7985() {
	if($content =~ /<b>Model Number<\/b><\/td>\W?<td><b>([\+\/0-9A-Za-z-]+)<\/b><\/td>/)
	 {
		print CSVOUTPUT ("CP-$1,");
		} else {
		print CSVOUTPUT ("N/A,");
	 }

	# Find the MAC Address
	if($content =~ /<b>MAC Address<\/b><\/td>\W?<td><b>([0-9A-Za-z-]+)<\/b><\/td>/)
	 {
	        print CSVOUTPUT ("$1,");
	        } else {
       		print CSVOUTPUT ("N/A,");
 	}

	# Find the Host Name
	if($content =~ /<b>Host Name<\/b><\/td>\W?<td><b>([0-9A-Za-z]+)<\/b><\/td>/)
	 {
	        print CSVOUTPUT ("$1,");
	        } else {
	        print CSVOUTPUT ("N/A,");
	 }

	# Find the Phone's DN
	if($content =~ /<b>Phone DN<\/b><\/td>\W?<td><b>([\+0-9A-Za-z-]+)<\/b><\/td>/)
	 {
	        print CSVOUTPUT ("$1,");
	        } else {
       		print CSVOUTPUT ("N/A,");
	 }

	# Find the Phone Load Version number
	if($content =~ /<b>App Load ID<\/b><\/td>\W?<td><b>([A-Za-z0-9\.\-\_]+)<\/b><\/td>/)
	 {
        	print CSVOUTPUT ("$1,");
	        } else {
        	print CSVOUTPUT ("N/A,");
	 }

	# Find the Phone Serial Number
	if($content =~ /<b>Serial Number<\/b><\/td>\W?<td><b>([0-9A-Za-z]+)<\/b><\/td>/)
	 {
	        print CSVOUTPUT ("$1,");
	        } else {
	        print CSVOUTPUT ("N/A,");
	 }
	# Print a newline to start a new record
	print CSVOUTPUT ("false\n");
} # End sub cp7985

#
# sub parse_xml - Primary subroutine to gather phone data
# Parses XML output from XML capable phones
#
sub parse_xml {
	my $xml = XML::Simple->new(SuppressEmpty => 1); # Setup XML::Simple and Ignore Empty Elements to avoid empty "HASH(0x....)" elements
	my $data = $xml->XMLin($content);		# Parse the XML data from the Main Device Web page
	if (exists $data->{modelNumber}) 	{ print CSVOUTPUT ("$data->{modelNumber},")	} else { print CSVOUTPUT ","};	# Model Number
	if (exists $data->{MACAddress}) 	{ print CSVOUTPUT ("$data->{MACAddress},")	} else { print CSVOUTPUT ","};	# MAC Address
	if (exists $data->{HostName})		{ print CSVOUTPUT ("$data->{HostName},")	} else { print CSVOUTPUT ","};	# Host Name
	if (exists $data->{phoneDN})		{ print CSVOUTPUT ("$data->{phoneDN},")		} else { print CSVOUTPUT ","};	# Find the Phone's DN
	if (exists $data->{appLoadID})		{ print CSVOUTPUT ("$data->{appLoadID},")	} else { print CSVOUTPUT ","};	# Find the Phone Load Version number
	if (exists $data->{serialNumber})	{ print CSVOUTPUT ("$data->{serialNumber},")} else { print CSVOUTPUT ","};	# Find the Phone Serial Number
	print CSVOUTPUT ("true");								# XML Capable
	if ($data->{modelNumber} =~ /CP-7921G|CP-7925G/) {		# CP-7921G and CP-7925G - Wireless phones
		print CSVOUTPUT ("\n");
	} elsif ($data->{modelNumber} =~ /CP-7940|CP-7960/) {		# CP-7960G and CP-7940G has a different XML format for the port information page
		my $PortData = $xml->XMLin($content_net);		# Parse the XML data from the Servicibility Web page on the phone (Works for most phones)
		if (exists $PortData->{deviceId})	{ print CSVOUTPUT (",$PortData->{deviceId},")	} else { print CSVOUTPUT ","};		# Switch Hostname
		if (exists $PortData->{ipAddress}) 	{ print CSVOUTPUT ("$PortData->{ipAddress},")	} else { print CSVOUTPUT ","};		# Switch IP Address
		print CSVOUTPUT (",");					# IPv6 is not a valid field for this phone type
		if (exists $PortData->{port})		{ print CSVOUTPUT ("$PortData->{port},")		} else { print CSVOUTPUT ","};		# Switch Switch Port
		print CSVOUTPUT ("LLDP Not Supported,");		# CP7960/7940's do not support LLDP
		print CSVOUTPUT ("LLDP Not Supported,");		# CP7960/7940's do not support LLDP
		print CSVOUTPUT ("LLDP Not Supported,");		# CP7960/7940's do not support LLDP
		print CSVOUTPUT ("LLDP Not Supported,");		# CP7960/7940's do not support LLDP
		if (exists $PortData->{PortSpeed}) {
			$PortData->{PortSpeed} =~ s/,\s+/,/;                    # Remove the Whitespace - Match the comma and one or more whitespace characters and replace with a comma
			print CSVOUTPUT ("$PortData->{PortSpeed},")										} else { print CSVOUTPUT ","};		# Switch Port Speed and Duplex
		if (exists $PortData->{PortInformation})	{ print CSVOUTPUT ("$PortData->{PortInformation}") } else { print CSVOUTPUT ","};	# Switch Port Information (Switch port Description? - needs testing)
		print CSVOUTPUT ("\n");					# Print a newline to start a new record
	} else {
		my $PortData = $xml->XMLin($content_net);		# Parse the XML data from the Servicibility Web page on the phone (Works for most phones)
		if (exists $PortData->{CDPNeighborDeviceId}) 		{ print CSVOUTPUT (",$PortData->{CDPNeighborDeviceId},")	} else { print CSVOUTPUT ","};	# Switch Hostname
		if (exists $PortData->{CDPNeighborIP})				{ print CSVOUTPUT ("$PortData->{CDPNeighborIP},") 			} else { print CSVOUTPUT ","};	# Switch IPv4 Address
		if (exists $PortData->{CDPNeighborIPv6})			{ print CSVOUTPUT ("$PortData->{CDPNeighborIPv6},")			} else { print CSVOUTPUT ","};	# Switch IPv6 Address
		if (exists $PortData->{CDPNeighborPort})			{ print CSVOUTPUT ("$PortData->{CDPNeighborPort},")			} else { print CSVOUTPUT ","};	# Switch Switch Port
		if (exists $PortData->{LLDPNeighborDeviceId})		{ print CSVOUTPUT ("$PortData->{LLDPNeighborDeviceId},")	} else { print CSVOUTPUT ","};	# LLDP Neighbor Switch Hostname
		if (exists $PortData->{LLDPNeighborIP})				{ print CSVOUTPUT ("$PortData->{LLDPNeighborIP},")			} else { print CSVOUTPUT ","};	# LLDP Neighbor Switch IP Address
		if (exists $PortData->{LLDPNeighborIPv6})			{ print CSVOUTPUT ("$PortData->{LLDPNeighborIPv6},")		} else { print CSVOUTPUT ","};	# LLDP Neighbor Switch IPv6 Address
		if (exists $PortData->{LLDPNeighborPort})			{ print CSVOUTPUT ("$PortData->{LLDPNeighborPort},")		} else { print CSVOUTPUT ","};	# LLDP Neighbor Switch Port
		if (exists $PortData->{PortSpeed}) {
			$PortData->{PortSpeed} =~ s/,\s+/,/;			# Remove the Whitespace - Match the comma and one or more whitespace characters and replace with a comma
			print CSVOUTPUT ("$PortData->{PortSpeed},")																	} else { print CSVOUTPUT ","};		# Switch Port Speed and Duplex cells
		if (exists $PortData->{PortInformation})			{ print CSVOUTPUT ("$PortData->{PortInformation}")			} else { print CSVOUTPUT ","};	# Switch Port Information (Switch port Description? - needs testing)
		print CSVOUTPUT ("\n");					# Print a newline to start a new record
	}
}

=head1 NAME

 cipit.pl

=head1 SYNOPSIS

 cipit.pl {-I IP Address/CIDR]} -i inputfile.txt -o outputfile.csv {-f} {-v} {-h} {-r n}

=head1 DESCRIPTION

 Fetch and write to comma separated values file the phone inventory list.

 cipit.pl works best with an input file of IP addresses.  It also includes
 a SYN/ACK subnet scanning method.  This method is not 100% accurate due to
 the inherent flaw of SYN/ACK scanning.

 Switches that define a value can be done in long or short form.
 eg:
   cipit.pl --inputfile someListofIPs.txt
   cipit.pl -i someListofIPs.txt

=head1 ARGUMENTS

 -I, --IP
 IP Addresses: Can be individual IPs or IP/CIDR format:
   10.1.243.111
   10.1.243.0/24
   10.1.243.4/30

 -i, --inputfile
 Filename that has one IP address per line. The input file should be a text
 file with one IP per line.  One way to create this input file is to cut
 and paste the Device Page of your Cisco CCM into a spreadsheet and remove
 the CCM server IPs.

	Alternatively if you are using CCME the following command works well:
 show ephone | redirect tftp://<yourTftpServerIP>/inputfilename.txt

 -r, --repeat
 Repeat the SYN/ACK/TCP Socket Connect a number of times.  Default = 2 for
 increased reliability.
	Usage: -r n
	Where "n" is the number of times to scan the IP subnet(s).

 -f, --force
 force overwrite of output file if exists.

 -v, --verbose
 Gives a lot more output

 -h, --help
 Shows the manual.


=head1 AUTHOR

 Vince Loschiavo
 https://sourceforge.net/projects/cipinventory/
 http://www.linkedin.com/in/vloschiavo

=head1 CREDITS

 Thanks to all those who have offered suggestions on how to improve
 the script:
  -Thanks to Alain for the French language testing
  -Special thanks to Simon Koch (from Panalpina Management Ltd.) for the feature suggestions
	and assistance testing and debugging v0.11


=head1 BUGS

 Have complete script failure on trying to handle wide characters in XML data. Otherwise, none that I know of. :)


=head1 TODO

 The Roadmap includes:

 -v0.12 	- CUCM v5,6,7,8,... (Linux versions) AXL/SOAP interface to CUCM via commandline option
 -v0.12		- Repair issues with UTF-8 encoding problems for wide characters.

=head1 UPDATES

 Last update on: 2012-JAN-18  23:00 PST

=cut
