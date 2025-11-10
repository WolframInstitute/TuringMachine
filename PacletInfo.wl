Paclet[
    Name -> "TuringMachineSearch",
    Version -> "0.1",
    Extensions -> {
        {
            "Cargo",
            "Root" -> "Libs/ndtm_search"
        },
        {
            "Build",
            "Actions" -> {"CargoBuild"}
        },
        {
            "Kernel", 
            "Root" -> ".", 
            "Context" -> "TuringMachineSearch`"
        },
        {
            "Binaries"
        }
    }
]