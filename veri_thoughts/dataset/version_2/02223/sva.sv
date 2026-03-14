module larger_number_sva (
    // Analysis: No clock/reset in DUT; pure combinational selection of max(num1,num2); equal selects num1.
    // Sampling clock/reset provided here for SVA only (active-low RESETn).
    input  logic        CLK,
    input  logic        RESETn,
    input  logic [3:0]  num1,
    input  logic [3:0]  num2,
    input  logic [3:0]  larger
);
    // If num1 > num2, output must equal num1.
    check_larger_is_num1_when_gt: assert property (
        @(posedge CLK) disable iff (!RESETn) (num1 > num2) |-> (larger == num1)
    );

    // If num2 > num1, output must equal num2.
    check_larger_is_num2_when_gt: assert property (
        @(posedge CLK) disable iff (!RESETn) (num2 > num1) |-> (larger == num2)
    );

    // If num1 == num2, output must equal num1 (tie breaks to num1).
    check_larger_is_num1_when_eq: assert property (
        @(posedge CLK) disable iff (!RESETn) (num1 == num2) |-> (larger == num1)
    );

    // Output must always equal one of the two inputs.
    check_output_is_one_of_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn) (larger == num1) || (larger == num2)
    );

    // If output selects num1 and inputs differ, then num1 must be greater.
    check_num1_selected_implies_gt: assert property (
        @(posedge CLK) disable iff (!RESETn) ((larger == num1) && (num1 != num2)) |-> (num1 > num2)
    );

    // If output selects num2 and inputs differ, then num2 must be greater.
    check_num2_selected_implies_gt: assert property (
        @(posedge CLK) disable iff (!RESETn) ((larger == num2) && (num1 != num2)) |-> (num2 > num1)
    );

    // When both inputs are stable across a cycle, the output must be stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(num1) && $stable(num2) |-> $stable(larger)
    );

    // Output value must be at least as large as each input (i.e., equals the max).
    check_output_is_at_least_each_input: assert property (
        @(posedge CLK) disable iff (!RESETn) (larger >= num1) && (larger >= num2)
    );

    // Output can change only if at least one input changed.
    check_output_change_requires_input_change: assert property (
        @(posedge CLK) disable iff (!RESETn) $changed(larger) |-> ($changed(num1) || $changed(num2))
    );
endmodule