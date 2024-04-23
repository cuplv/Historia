FROM ubuntu:20.04 
RUN apt-get update

ENV DEBIAN_FRONTEND=noninteractive
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone

#Infer dependencies
RUN apt-get install -y gcc make sudo cmake binutils g++ curl opam wget pkg-config sqlite  automake autoconf libgmp-dev libsqlite3-dev zlib1g-dev
RUN apt-get update && apt-get install -y openjdk-17-jdk

# Setup Infer
RUN opam init --reinit --bare --disable-sandboxing --yes --auto-setup # disable sandboxing while in a container
RUN git clone https://github.com/facebook/infer.git
RUN cd infer && git reset --hard 6cd0f3 && ./build-infer.sh java
RUN cd infer && sudo make install

## Android SDK
# Set up environment variables
ENV ANDROID_HOME="/root/android-sdk-linux" \
    SDK_URL="https://dl.google.com/android/repository/commandlinetools-linux-6858069_latest.zip" \
    GRADLE_URL="https://services.gradle.org/distributions/gradle-4.5.1-all.zip"

#SDK_URL="https://dl.google.com/android/repository/sdk-tools-linux-3859397.zip" \

# Install Gradle
RUN cd /root \
  && wget $GRADLE_URL -O gradle.zip \
  && unzip gradle.zip \
  && mv gradle-4.5.1 gradle \
  && rm gradle.zip \
  && mkdir .gradle

ENV PATH="/root/gradle/bin:${ANDROID_HOME}/cmdline-tools:${ANDROID_HOME}/platform-tools:${PATH}"

#ENV JAVA_OPTS="-XX:+IgnoreUnrecognizedVMOptions --add-modules java.se.ee"

# Download Android SDK
RUN mkdir "$ANDROID_HOME" .android \
  && cd "$ANDROID_HOME" \
  && curl -o sdk.zip $SDK_URL \
  && unzip sdk.zip \
  && rm sdk.zip \
  && cd $ANDROID_HOME/cmdline-tools/bin \
  && yes | ./sdkmanager --licenses --sdk_root=$ANDROID_HOME #\
  && touch /root/.android/repositories.cfg

# Install platform tools
RUN cd /root/android-sdk-linux/cmdline-tools/bin \
    && ./sdkmanager --sdk_root=$ANDROID_HOME "platform-tools"  "platforms;android-16" "platforms;android-17" "platforms;android-18" "platforms;android-19" "platforms;android-20" "platforms;android-21" "platforms;android-22" "platforms;android-23" "platforms;android-24" "platforms;android-25" "platforms;android-26" "platforms;android-27" "platforms;android-7" "platforms;android-8" "platforms;android-9" "platforms;android-30"
#
RUN  cd /root/android-sdk-linux/cmdline-tools/bin \
    && ./sdkmanager --sdk_root=$ANDROID_HOME "platforms;android-29"
COPY testApps/ChatGPT_Benchmarks/ testApps/ChatGPT_Benchmarks/
RUN rm -rf testApps/ChatGPT_Benchmarks/EXN_nullptr/app_bug/infer-out/ #buggy folder why does it exist?
RUN apt-get install -y python3
COPY runPulse.py .