CREATE TABLE jobs(
	id SERIAL PRIMARY KEY,
	status varchar, 
	config varchar, 
	started timestamp without time zone,
        ended timestamp without time zone,
	owner varchar,
	stderr varchar,
	stdout varchar
);
CREATE TABLE results(
	id SERIAL PRIMARY KEY,
	jobid integer,
	qry varchar,
	result varchar,
	resultdata int,
	apkhash varchar,
	bounderjarhash varchar,
	owner varchar
);
CREATE TABLE apks (apkname text, img bytea);
CREATE TABLE resultdata(
	id SERIAL PRIMARY KEY,
	data bytea
);
