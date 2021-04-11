CREATE TABLE jobs(
	id integer, 
	status varchar(20), 
	config varchar, 
	PRIMARY KEY(id)
);
CREATE TABLE results(
	jobid integer,
	qry varchar,
	result varchar,
	stderr varchar,
	stdout varchar
);
CREATE TABLE apks (apkname text, img bytea);
