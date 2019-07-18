pipeline {
  agent {
    dockerfile {
      additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
    }
  }
  options {
    ansiColor('xterm')
  }
  stages {
    stage("Init title") {
      when { changeRequest() }
      steps {
        script {
          currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}"
        }
      }
    }
    stage('Build') {
      steps {
        ansiColor('xterm') {
          sh '''#!/bin/bash
            ./build kink .build/kbackend-haskell
          '''
        }
      }
    }
    stage('t/foobar') { steps {  sh '''./build t/foobar''' } }
    stage('t/peano')  { steps {  sh '''./build t/peano'''  } }
    stage('t/imp')    { steps {  sh '''./build t/imp'''    } }

    // Catch-all for anything left out
    stage('t/*')      { steps {  sh '''./build'''          } }
  }
}
