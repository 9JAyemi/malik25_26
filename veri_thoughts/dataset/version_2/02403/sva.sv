module nios_dut_pio_2_sva (
    input  logic        clk,
    input  logic        reset_n,   // active-low
    input  logic [1:0]  address,
    input  logic [19:0] in_port,
    input  logic [31:0] readdata
);
    ///// Reset behavior /////
    // During reset, readdata must be 0.
    check_reset_clears_readdata: assert property (
        @(posedge clk) !reset_n |-> (readdata == 32'h0)
    );

    ///// Output formatting /////
    // Upper 12 bits of readdata are always zero when not in reset.
    check_readdata_upper_zero: assert property (
        @(posedge clk) disable iff (!reset_n) readdata[31:20] == 12'b0
    );

    ///// Functional updates (registered with one-cycle latency) /////
    // Next-cycle readdata equals zero-extended in_port when previous address was 2'b00.
    check_update_on_addr_00: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) && ($past(address) == 2'b00) |->
                (readdata == {12'b0, $past(in_port)})
    );

    // Next-cycle readdata equals zero-extended in_port when previous address was 2'b01.
    check_update_on_addr_01: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) && ($past(address) == 2'b01) |->
                (readdata == {12'b0, $past(in_port)})
    );

    // Next-cycle readdata is zero when previous address was 2'b10 or 2'b11.
    check_update_on_addr_other_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) && ($past(address) inside {2'b10,2'b11}) |->
                (readdata == 32'h0)
    );

    // Consolidated model: next-cycle readdata matches decode of previous address/in_port.
    check_readdata_matches_model: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) |->
                (readdata == {12'b0, (($past(address) inside {2'b00,2'b01}) ? $past(in_port) : 20'b0)})
    );
endmodule