module manufacturing_process_controller(

    input wire clk,

    //input events
    input wire InjectorArmFinishMovement_eI,
    input wire EmergencyStopChanged_eI,
    input wire CanisterPressureChanged_eI,
    input wire FillContentsAvailableChanged_eI,
    input wire LasersChanged_eI,
    input wire DoorOverride_eI,
    input wire VacuumTimerElapsed_eI,

    //output events
    output wire DoorReleaseCanister_eO,
    output wire ConveyorChanged_eO,
    output wire InjectorPositionChanged_eO,
    output wire InjectorControlsChanged_eO,
    output wire FillContentsChanged_eO,
    output wire StartVacuumTimer_eO,
    output wire GoRejectArm_eO,
    output wire CanisterCountChanged_eO,
    output wire InjectDone_eO,

    //input variables
    input wire EmergencyStop_I,
    input wire [7:0] CanisterPressure_I,
    input wire [7:0] FillContentsAvailable_I,
    input wire DoorSiteLaser_I,
    input wire InjectSiteLaser_I,
    input wire RejectSiteLaser_I,
    input wire RejectBinLaser_I,
    input wire AcceptBinLaser_I,

    //output variables
    output wire [7:0] ConveyorSpeed_O ,
    output wire [7:0] InjectorPosition_O ,
    output wire InjectorContentsValveOpen_O ,
    output wire InjectorVacuumRun_O ,
    output wire InjectorPressurePumpRun_O ,
    output wire [7:0] FillContents_O ,
    output wire [7:0] CanisterCount_O ,

    input reset
);

    // Declare internal variables
    reg [7:0] conveyor_speed;
    reg [7:0] injector_position;
    reg injector_contents_valve_open;
    reg injector_vacuum_run;
    reg injector_pressure_pump_run;
    reg [7:0] fill_contents;
    reg [7:0] canister_count;
    reg inject_done;
    reg door_release_canister;
    reg conveyor_changed;
    reg injector_position_changed;
    reg injector_controls_changed;
    reg fill_contents_changed;
    reg start_vacuum_timer;
    reg go_reject_arm;
    reg canister_count_changed;

    // Process input events and variables
    always @(posedge clk, posedge reset) begin
        if (reset) begin
            conveyor_speed <= 0;
            injector_position <= 0;
            injector_contents_valve_open <= 0;
            injector_vacuum_run <= 0;
            injector_pressure_pump_run <= 0;
            fill_contents <= 0;
            canister_count <= 0;
            inject_done <= 0;
            door_release_canister <= 0;
            conveyor_changed <= 0;
            injector_position_changed <= 0;
            injector_controls_changed <= 0;
            fill_contents_changed <= 0;
            start_vacuum_timer <= 0;
            go_reject_arm <= 0;
            canister_count_changed <= 0;
        end else begin
            if (EmergencyStopChanged_eI) begin
                if (EmergencyStop_I) begin
                    conveyor_speed <= 0;
                    injector_vacuum_run <= 0;
                    injector_pressure_pump_run <= 0;
                end
            end
            if (CanisterPressureChanged_eI) begin
                if (CanisterPressure_I > 200) begin
                    conveyor_speed <= conveyor_speed + 1;
                    conveyor_changed <= 1;
                end
            end
            if (FillContentsAvailableChanged_eI) begin
                fill_contents <= FillContentsAvailable_I;
                fill_contents_changed <= 1;
            end
            if (LasersChanged_eI) begin
                if (DoorSiteLaser_I == 1 && RejectSiteLaser_I == 1) begin
                    door_release_canister <= 1;
                end
                if (InjectSiteLaser_I == 1) begin
                    injector_position <= 255;
                    injector_position_changed <= 1;
                end
                if (RejectBinLaser_I == 1) begin
                    go_reject_arm <= 1;
                end
                if (AcceptBinLaser_I == 1) begin
                    canister_count <= canister_count + 1;
                    canister_count_changed <= 1;
                end
            end
            if (VacuumTimerElapsed_eI) begin
                start_vacuum_timer <= 0;
                injector_contents_valve_open <= 0;
                injector_vacuum_run <= 0;
                inject_done <= 1;
                injector_controls_changed <= 1;
            end
            if (InjectorArmFinishMovement_eI) begin
                injector_contents_valve_open <= 1;
                injector_vacuum_run <= 1;
                injector_pressure_pump_run <= 1;
                start_vacuum_timer <= 1;
                injector_controls_changed <= 1;
            end
            if (DoorOverride_eI) begin
                door_release_canister <= 1;
            end
        end
    end

    // Assign output events and variables
    assign ConveyorSpeed_O = conveyor_speed;
    assign InjectorPosition_O = injector_position;
    assign InjectorContentsValveOpen_O = injector_contents_valve_open;
    assign InjectorVacuumRun_O = injector_vacuum_run;
    assign InjectorPressurePumpRun_O = injector_pressure_pump_run;
    assign FillContents_O = fill_contents;
    assign CanisterCount_O = canister_count;
    assign InjectDone_eO = inject_done;
    assign DoorReleaseCanister_eO = door_release_canister;
    assign ConveyorChanged_eO = conveyor_changed;
    assign InjectorPositionChanged_eO = injector_position_changed;
    assign InjectorControlsChanged_eO = injector_controls_changed;
    assign FillContentsChanged_eO = fill_contents_changed;
    assign StartVacuumTimer_eO = start_vacuum_timer;
    assign GoRejectArm_eO = go_reject_arm;
    assign CanisterCountChanged_eO = canister_count_changed;

endmodule