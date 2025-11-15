Paclet[
    Name -> "TuringMachineSearch",
    Version -> "0.2",
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
            "Root" -> "Kernel", 
            "Context" -> "TuringMachineSearch`"
        },
        {
            "Binaries"
        }
    }
]