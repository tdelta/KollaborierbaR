pipeline {
    agent any
    stages {
        stage('Setup') {
            steps {
              sh 'make setup'
            }
        }
        stage('Build') {
            steps {
              sh 'make'
            }
        }
    }
}
