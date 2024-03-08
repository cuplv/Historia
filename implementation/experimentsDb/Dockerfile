FROM postgres

ENV POSTGRES_PASSWORD=password 
RUN mkdir /dbsetup
COPY ./* /dbsetup/
COPY init-user-db.sh /docker-entrypoint-initdb.d/init-user-db.sh
#RUN cd /dbsetup/; ./createTablesPg.sh
