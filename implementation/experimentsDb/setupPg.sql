CREATE TABLE jobs(
	id SERIAL PRIMARY KEY,
	status varchar, 
	config varchar, 
	started timestamp without time zone,
        ended timestamp without time zone,
	owner varchar,
	stderr varchar,
	stdout varchar,
	jobtag varchar,
        inputid int
);
CREATE TABLE results(
	id SERIAL PRIMARY KEY,
	jobid integer,
	qry varchar,
	loc varchar,
	result varchar,
	querytime integer,
	resultdata int,
	apkhash varchar,
	bounderjarhash varchar,
	owner varchar,
	jobtag varchar
);
CREATE TABLE resultdata(
	id SERIAL PRIMARY KEY,
	data bytea
);
CREATE TABLE inputs (
	id SERIAL PRIMARY KEY,
	bounderjar varchar, 
	specfile varchar,
	notes varchar
);
CREATE TABLE apks (apkname text, img bytea);
