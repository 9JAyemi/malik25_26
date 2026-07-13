module password_protected_system_sva (
    input logic clk,
    input logic d,
    input logic [255:0] password,
    input logic [2:0] sel,
    input logic out
);

    // password[0] low forces the final ANDed output low.
    check_password0_gates_output: assert property (
        @(posedge clk) (password[0] == 1'b0) |-> (out == 1'b0)
    );

    // Low selector bits 00 use the newest shifted data bit.
    check_sel0_uses_shift_stage0: assert property (
        @(posedge clk)
        (!$initstate && (sel[1:0] == 2'b00))
        |-> (out == (password[0] & ($past(d, 1) == password[0])))
    );

    // Low selector bits 01 use the next older shifted data bit.
    check_sel1_uses_shift_stage1: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate) && (sel[1:0] == 2'b01))
        |-> (out == (password[0] & ($past(d, 2) == password[1])))
    );

    // Low selector bits 10 use the oldest valid shifted data bit.
    check_sel2_uses_shift_stage2: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate) && !$past($initstate, 2) && (sel[1:0] == 2'b10))
        |-> (out == (password[0] & ($past(d, 3) == password[2])))
    );

endmodule