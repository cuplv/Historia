CREATE TABLE jobs(
	id SERIAL PRIMARY KEY,
	status varchar(20), 
	config varchar, 
	started timestamp without time zone,
        ended timestamp without time zone,
	owner varchar
);
CREATE TABLE results(
	id SERIAL PRIMARY KEY,
	jobid integer,
	qry varchar,
	result varchar,
	stderr varchar,
	stdout varchar,
	resultdata int,
	apkHash varchar,
	bounderJarHash varchar,
	owner varchar
);
CREATE TABLE apks (apkname text, img bytea);
CREATE TABLE resultdata(
	id SERIAL PRIMARY KEY,
	data bytea
);
