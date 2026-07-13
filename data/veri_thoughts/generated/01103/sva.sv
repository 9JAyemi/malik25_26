module barrel_shifter_sva (
    input logic CLK,              // sampling clock for assertions (DUT has no clock/reset)
    input logic [3:0] in,
    input logic [1:0] shift_amt,
    input logic dir,
    input logic [3:0] out
);
    // DUT is pure combinational: dir==0 => out=in<<shift_amt; dir==1 => out=in>>shift_amt.

    // Out equals the selected shift function of inputs each cycle.
    check_out_comb_function: assert property (
        @(posedge CLK) out == (dir ? (in >> shift_amt) : (in << shift_amt))
    );

    // Shift-by-zero is a passthrough regardless of direction.
    check_shift0_passthrough: assert property (
        @(posedge CLK) (shift_amt == 2'd0) |-> (out == in)
    );

    // When inputs are stable, output remains stable (pure function property).
    check_stable_output_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(in) && $stable(shift_amt) && $stable(dir)) |-> $stable(out)
    );

    // Left shift by 1: LSB becomes 0; upper bits shift up by one.
    check_left_shift_by1: assert property (
        @(posedge CLK) (dir == 1'b0 && shift_amt == 2'd1) |-> (out[0] == 1'b0 && out[3:1] == in[2:0])
    );

    // Left shift by 2: two LSBs become 0; upper two bits shift up by two.
    check_left_shift_by2: assert property (
        @(posedge CLK) (dir == 1'b0 && shift_amt == 2'd2) |-> (out[1:0] == 2'b00 && out[3:2] == in[1:0])
    );

    // Left shift by 3: lower three bits become 0; MSB takes in[0].
    check_left_shift_by3: assert property (
        @(posedge CLK) (dir == 1'b0 && shift_amt == 2'd3) |-> (out[2:0] == 3'b000 && out[3] == in[0])
    );

    // Right shift by 1: MSB becomes 0; lower bits shift down by one.
    check_right_shift_by1: assert property (
        @(posedge CLK) (dir == 1'b1 && shift_amt == 2'd1) |-> (out[3] == 1'b0 && out[2:0] == in[3:1])
    );

    // Right shift by 2: two MSBs become 0; lower two bits shift down by two.
    check_right_shift_by2: assert property (
        @(posedge CLK) (dir == 1'b1 && shift_amt == 2'd2) |-> (out[3:2] == 2'b00 && out[1:0] == in[3:2])
    );

    // Right shift by 3: upper three bits become 0; LSB takes in[3].
    check_right_shift_by3: assert property (
        @(posedge CLK) (dir == 1'b1 && shift_amt == 2'd3) |-> (out[3:1] == 3'b000 && out[0] == in[3])
    );

endmodule