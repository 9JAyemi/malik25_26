module d_ff_en_parameterized_sva #(parameter WIDTH = 32) (
    input  logic [WIDTH-1:0] D,
    input  logic             CLK,
    input  logic             FSM_sequential_state_reg_reg_1,
    input  logic             FSM_sequential_state_reg_reg_2,
    input  logic [WIDTH-1:0] Q
);

    // When clear is asserted, Q becomes zero on the next clock.
    check_sync_clear_next: assert property (
        @(posedge CLK) FSM_sequential_state_reg_reg_1 |=> (Q == {WIDTH{1'b0}})
    );

    // When both clear and enable are high, clear dominates and Q becomes zero next cycle.
    check_clear_over_enable_priority: assert property (
        @(posedge CLK) (FSM_sequential_state_reg_reg_1 && FSM_sequential_state_reg_reg_2) |=> (Q == {WIDTH{1'b0}})
    );

    // When enable is high and clear is low, Q loads D sampled in the same cycle (observed next cycle).
    property load_on_enable_no_clear;
        logic [WIDTH-1:0] d_samp;
        @(posedge CLK) (!FSM_sequential_state_reg_reg_1 && FSM_sequential_state_reg_reg_2, d_samp = D) |=> (Q == d_samp);
    endproperty
    check_load_on_enable_no_clear: assert property (load_on_enable_no_clear);

    // When both clear and enable are low, Q holds its value across the next cycle.
    check_hold_when_idle: assert property (
        @(posedge CLK) (!FSM_sequential_state_reg_reg_1 && !FSM_sequential_state_reg_reg_2) |-> $stable(Q)
    );

    // Q only changes value across cycles if either clear or enable was asserted in the prior cycle.
    check_update_only_with_control: assert property (
        @(posedge CLK) (Q != $past(Q)) |-> ($past(FSM_sequential_state_reg_reg_1) || ($past(FSM_sequential_state_reg_reg_2) && !$past(FSM_sequential_state_reg_reg_1)))
    );

    // After a load (enable without clear), if controls go idle next cycle, Q equals the loaded D.
    property hold_loaded_value_when_idle_next;
        logic [WIDTH-1:0] d_samp2;
        @(posedge CLK) (!FSM_sequential_state_reg_reg_1 && FSM_sequential_state_reg_reg_2, d_samp2 = D) ##1
                       (!FSM_sequential_state_reg_reg_1 && !FSM_sequential_state_reg_reg_2) |-> (Q == d_samp2);
    endproperty
    check_hold_loaded_value_when_idle_next: assert property (hold_loaded_value_when_idle_next);

endmodule