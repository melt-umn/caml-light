#!groovy

library "github.com/melt-umn/jenkins-lib"

melt.setProperties(silverBase: true)

node {
try {

  def newenv = silver.getSilverEnv()

  stage ("Checkout") {
    checkout scm
    melt.clearGenerated()
  }

  stage ("Build") {
    // For this project, re-using 'generated' gains as much as parallelism, so don't bother
    withEnv(newenv) {
      sh "./silver-compile"
    }
  }

  stage("Test") {
    def examples=['sample_programs/btree.demo',
                  'sample_programs/if_example.demo',
                  'sample_programs/let_examples.demo',
                  'sample_programs/list.demo']

    def tasks = [:]
    tasks << examples.collectEntries { t -> [(t): task_test(t, newenv)] }
    
    parallel tasks
  }

  /* If we've gotten all this way with a successful build, don't take up disk space */
  melt.clearGenerated()
}
catch (e) {
  melt.handle(e)
}
finally {
  melt.notify(job: 'caml-light')
}
} // node

def task_test(String example, newenv){

  def exts_base = env.WORKSPACE

  return {
    // Each parallel task executes in a seperate node
    node {
      melt.clearGenerated()      
      withEnv(newenv) {
        sh "java -jar camlLight.jar ${example}"
      }
    }
  }
}
