module lights_switches_assertions (
    input logic [1:0]  address,
    input logic        clk,
    input logic [7:0]  in_port,
    input logic        reset_n,
    input logic [31:0] readdata
);

    // Active-low reset forces readdata low.
    check_reset_clears_readdata: assert property (
        @(posedge clk) !reset_n |-> (readdata == 32'b0)
    );

    // Upper 24 bits stay zero after each enabled clock.
    check_upper_bits_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        1'b1 |=> (readdata[31:8] == 24'b0)
    );

    // Nonzero addresses produce zero on the next sampled cycle.
    check_nonzero_address_returns_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address != 2'b00) |=> (readdata == 32'b0)
    );

    // Address 0 can only return zero or the prior input byte.
    check_addr0_returns_zero_or_input: assert property (
        @(posedge clk) disable iff (!reset_n)
        (address == 2'b00) |=> ((readdata == 32'b0) || (readdata == {24'b0, $past(in_port)}))
    );

    // After an enabled clock, readdata is zero or a zero-extended prior input.
    check_readdata_is_zero_or_prior_input: assert property (
        @(posedge clk) disable iff (!reset_n)
        1'b1 |=> ((readdata == 32'b0) || (($past(address) == 2'b00) && (readdata == {24'b0, $past(in_port)})))
    );

    // Zero input at address 0 yields zero on the next sampled cycle.
    check_zero_input_returns_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        ((address == 2'b00) && (in_port == 8'h00)) |=> (readdata == 32'b0)
    );

endmodule