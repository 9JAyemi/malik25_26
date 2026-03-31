```systemverilog
module sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg_sva (
    input logic CLK,
    input logic SLEEP_B,
    output logic X
);
    // SLEEP_B is inverted to SLEEP
    sleep_inversion: assert property (
        @(posedge CLK) disable iff (!SLEEP_B) SLEEP == 1'b0
    );
    sleep_inversion_2: assert property (
        @(posedge CLK) disable iff (SLEEP_B) SLEEP == 1'b1
    );

    // X is driven by the AND of SLEEP_B and A
    x_driven_by_and: assert property (
        @(posedge CLK) disable iff (!SLEEP_B) X == (SLEEP_B & A)
    );
endmodule
```