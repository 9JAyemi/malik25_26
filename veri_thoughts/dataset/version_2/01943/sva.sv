module nios_system_switches_sva (
    input logic        clk,
    input logic        reset_n,    // active-low, async in RTL
    input logic [1:0]  address,
    input logic [9:0]  in_port,
    input logic [31:0] readdata
);
    // Clock: clk (posedge). Logic: combinational mux into a registered 32-bit output.

    // During reset, readdata must be cleared to 0.
    reset_clears_readdata: assert property (
        @(posedge clk) (!reset_n) |-> (readdata == 32'd0)
    );

    // After one cycle out of reset, upper 22 bits are always zero (zero-extension).
    upper_bits_zero_postreset: assert property (
        @(posedge clk) disable iff (!reset_n) $past(reset_n) |-> (readdata[31:10] == 22'd0)
    );

    // After one cycle out of reset, LSBs equal prior-cycle muxed input: (address==0)? in_port : 0.
    lsb_matches_masked_in_port: assert property (
        @(posedge clk) disable iff (!reset_n) $past(reset_n) |-> (readdata[9:0] == $past((address == 2'b00) ? in_port : 10'd0))
    );

    // When prior address was 0, full word is zero-extended prior in_port.
    full_word_zeroext_on_addr00: assert property (
        @(posedge clk) disable iff (!reset_n) $past(reset_n) && ($past(address) == 2'b00) |-> (readdata == {22'd0, $past(in_port)})
    );

    // When prior address was not 0, the full word must be zero.
    full_word_zero_when_addr_not00: assert property (
        @(posedge clk) disable iff (!reset_n) $past(reset_n) && ($past(address) != 2'b00) |-> (readdata == 32'd0)
    );

    // Nonzero LSBs imply prior address selected the port (address==0).
    lsb_nonzero_implies_addr00: assert property (
        @(posedge clk) disable iff (!reset_n) $past(reset_n) && (readdata[9:0] != 10'd0) |-> ($past(address) == 2'b00)
    );
endmodule