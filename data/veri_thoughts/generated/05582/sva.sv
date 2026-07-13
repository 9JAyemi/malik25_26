module top_module_sva (
    input logic        clk,
    input logic [15:0] DATA,
    input logic [3:0]  SHIFT,
    input logic [1:0]  CTRL,
    input logic [3:0]  binary,
    input logic [15:0] out
);

    // Output matches the implemented top-level combinational function.
    check_out_matches_top_logic: assert property (
        @(posedge clk)
        out == ~(((CTRL == 2'b10) ? {16{DATA[15]}} :
                  (CTRL == 2'b00) ? DATA :
                  (CTRL == 2'b01) ? (DATA << SHIFT) :
                  (CTRL == 2'b11) ? (DATA >> SHIFT) :
                  DATA))
    );

    // CTRL=00 passes DATA through before the final inversion.
    check_ctrl00_passthrough: assert property (
        @(posedge clk)
        (CTRL == 2'b00) |-> (out == ~DATA)
    );

    // CTRL=01 left shifts DATA before the final inversion.
    check_ctrl01_left_shift: assert property (
        @(posedge clk)
        (CTRL == 2'b01) |-> (out == ~(DATA << SHIFT))
    );

    // CTRL=10 replicates DATA[15] before the final inversion.
    check_ctrl10_sign_replicate: assert property (
        @(posedge clk)
        (CTRL == 2'b10) |-> (out == {16{~DATA[15]}})
    );

    // CTRL=11 right shifts DATA before the final inversion.
    check_ctrl11_right_shift: assert property (
        @(posedge clk)
        (CTRL == 2'b11) |-> (out == ~(DATA >> SHIFT))
    );

    // A zero left-shift amount leaves DATA unchanged before inversion.
    check_ctrl01_shift_zero: assert property (
        @(posedge clk)
        (CTRL == 2'b01 && SHIFT == 4'd0) |-> (out == ~DATA)
    );

    // A zero right-shift amount leaves DATA unchanged before inversion.
    check_ctrl11_shift_zero: assert property (
        @(posedge clk)
        (CTRL == 2'b11 && SHIFT == 4'd0) |-> (out == ~DATA)
    );

endmodule