# Cisco IP Phone Inventory Tool (CIPIT)
This Script was originally written by Vince Loschiavo on 2012-JAN-03

Original project: https://sourceforge.net/projects/cipinventory/

New branch author: Michael Randolph on 2016-OCT-13

if you enjoy it or have comments/suggestions
  email: <first name> + <c> + <last name> @ gmail d0t com

Follow new project branch on GitHub

New project branch:
https://github.com/michaelcrandolph/Cisco-IP-Phone-Inventory-Tool

This script was tested with Cisco SCCP images:
---
* CP-6921G
* CP-7905G / CP-7906G
* CP-7910G / CP-7911G / CP-7912G / CP-7920 / CP-7921G / CP-7925G / CP-7925G-E
* CP-7935 - Tested and Not working
* CP-7936 - Tested and Not working
* CP-7937G / CP-7940G / CP-7941G / CP-7942G / CP-7945G
* CP-7960G / CP-7961G / CP-7962G / CP-7965G / CP-7970G / CP-7971G-G / CP-7975G / CP-7985G
* CP-9951 / CP-9971

When Reading from a File of IP Addresses:
* Includes Duplicate IP checking
* Reporting on Phones not responding

General:
---
* Now parses phone XML for greater portability across localizations. Tested on: English, French, and Chinese localizations
* Overwrite file check
* Progress indicator to let you know it's actually doing something
* Calculate execution time
* CIDR IP Address Entry from Commandline
* Improved overall speed

 By using:
 * TCP/Syn-ACK Echo to test IP Reachability
 * IO::Socket::INET to test if TCP port 80/443 is open
* IP Addresses sorted in output file
* Included warning for CIDR less than /23 as this can put a lot of load on your network.
* Verbose Option to see the action
* Better (-h --help) help options and output
* Commandline option for multiple iterations through the SYN/ACK discovery process for greater accuracy
* Future: Add support for HTTPS
