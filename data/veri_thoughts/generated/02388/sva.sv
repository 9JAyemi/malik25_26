module twos_complement_sva (
    input logic CLK,
    input logic [3:0] in,
    input logic [3:0] out
);
    // Clock: CLK (posedge). No reset present. Sequential reg out with 1-cycle latency; out <= (~in)+1.

    // Next cycle out equals two's complement of current in.
    property p_out_is_twos_complement;
        logic [3:0] vin;
        @(posedge CLK) (vin = in, 1'b1) ##1 (out == (~vin) + 4'd1);
    endproperty
    check_out_is_twos_complement: assert property (p_out_is_twos_complement);

    // Next cycle out plus prior in wraps to zero (mod 16).
    property p_out_plus_in_is_zero;
        logic [3:0] vin;
        @(posedge CLK) (vin = in, 1'b1) ##1 ((out + vin) == 4'd0);
    endproperty
    check_out_plus_in_zero: assert property (p_out_plus_in_is_zero);

    // If in is 0, next cycle out is 0.
    check_zero_maps_to_zero: assert property (
        @(posedge CLK) (in == 4'd0) |=> (out == 4'd0)
    );

    // If in is 8 (1000), next cycle out is also 8 (self-negating).
    check_eight_maps_to_eight: assert property (
        @(posedge CLK) (in == 4'd8) |=> (out == 4'd8)
    );

    // If in is 1, next cycle out is 15.
    check_one_maps_to_fifteen: assert property (
        @(posedge CLK) (in == 4'd1) |=> (out == 4'd15)
    );

    // If in is 15, next cycle out is 1.
    check_fifteen_maps_to_one: assert property (
        @(posedge CLK) (in == 4'd15) |=> (out == 4'd1)
    );

    // Non-zero in implies next cycle out is non-zero.
    check_nonzero_in_implies_nonzero_out: assert property (
        @(posedge CLK) (in != 4'd0) |=> (out != 4'd0)
    );

    // LSB is preserved through two's complement: if in[0]==1, next out[0]==1.
    check_lsb_preserved_one: assert property (
        @(posedge CLK) (in[0] == 1'b1) |=> (out[0] == 1'b1)
    );

    // LSB is preserved through two's complement: if in[0]==0, next out[0]==0.
    check_lsb_preserved_zero: assert property (
        @(posedge CLK) (in[0] == 1'b0) |=> (out[0] == 1'b0)
    );

endmodule