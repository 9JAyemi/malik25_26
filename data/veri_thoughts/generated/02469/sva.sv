module Mux_3x1_sva (
    input logic clk,
    input logic [1:0] ctrl,
    input logic [7:0] D0,
    input logic [7:0] D1,
    input logic [7:0] D2,
    input logic [7:0] S
);
    // ctrl==00 selects D0.
    check_ctrl_00_selects_D0: assert property (
        @(posedge clk) (ctrl == 2'b00) |-> (S == D0)
    );

    // ctrl==01 selects D1.
    check_ctrl_01_selects_D1: assert property (
        @(posedge clk) (ctrl == 2'b01) |-> (S == D1)
    );

    // ctrl==10 selects D2.
    check_ctrl_10_selects_D2: assert property (
        @(posedge clk) (ctrl == 2'b10) |-> (S == D2)
    );

    // ctrl==11 drives zero (default case).
    check_ctrl_11_selects_zero: assert property (
        @(posedge clk) (ctrl == 2'b11) |-> (S == 8'b0)
    );

    // Exact functional equivalence to the case statement.
    check_function_equivalence: assert property (
        @(posedge clk)
            S == ((ctrl == 2'b00) ? D0 :
                  (ctrl == 2'b01) ? D1 :
                  (ctrl == 2'b10) ? D2 : 8'b0)
    );

    // Output remains stable if all inputs and select remain stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) $stable(ctrl) && $stable(D0) && $stable(D1) && $stable(D2) |-> $stable(S)
    );

    // Output changes only if ctrl or one of the inputs changes.
    check_output_change_implies_input_change: assert property (
        @(posedge clk) !$stable(S) |-> (!$stable(ctrl) || !$stable(D0) || !$stable(D1) || !$stable(D2))
    );
endmodule