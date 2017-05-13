#!/bin/bash

set -e

# Print statistics about how well code is commented

tmp=$(mktemp -t "cloc.sql")

cloc --quiet --vcs=git -sql="$tmp"
sqlite3 -cmd ".read \"$tmp\"" -cmd '.headers on' -cmd '.width 38' -column <<EOF
select File, nCode+nComment as "code lines",
	round(cast(nComment as float)/(nCode+nComment), 2) as "% comments"
	from t
	where Language = "Coq"
	order by "% comments" asc, "code lines" desc;

.print ""

select sum(nCode+nComment) as "total lines",
	sum(nComment) as "total comments",
	round(sum(cast(nComment as float))/sum(nCode+nComment), 2) as "% comments"
	from t
	where Language = "Coq";

.print ""

select File, nCode+nComment as "code lines",
	round(cast(nComment as float)/(nCode+nComment), 2) as "% comments"
	from t
	where Language = "Haskell"
	order by "% comments" asc, "code lines" desc;

.print ""

select sum(nCode+nComment) as "total Haskell lines",
	sum(nComment) as "total comments",
	round(sum(cast(nComment as float))/sum(nCode+nComment), 2) as "% comments"
	from t
	where Language = "Haskell";
EOF

rm -f "$tmp"
