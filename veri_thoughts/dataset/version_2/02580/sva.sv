module decoder_barrelshifter_sva (
    input  logic       A,
    input  logic       B,
    input  logic       C,
    input  logic [3:0] data_in,
    input  logic       dir,
    input  logic [3:0] data_out
);

    // Local recomputation of DUT combinational function
    logic        passthrough;         // A & ~B & ~C selects pass-through
    logic [3:0]  left_shifted;        // data_in << 1
    logic [3:0]  right_shifted;       // data_in >> 1
    logic [3:0]  expected_shifted;    // dir ? right : left

    assign passthrough      = (A & ~B & ~C);
    assign left_shifted     = data_in << 1;
    assign right_shifted    = data_in >> 1;
    assign expected_shifted = dir ? right_shifted : left_shifted;

    // data_out matches exact RTL expression (pass-through vs shifted)
    check_function_equivalence: assert property (
        @(posedge A) data_out == (passthrough ? data_in : expected_shifted)
    );

    // Pass-through case: when A&~B&~C, output equals input
    check_passthrough: assert property (
        @(posedge A) passthrough |-> (data_out == data_in)
    );

    // Shift-left case: when not pass-through and dir==0, output equals data_in<<1
    check_shift_left_vector: assert property (
        @(posedge A) (!passthrough && (dir == 1'b0)) |-> (data_out == left_shifted)
    );

    // Shift-right case: when not pass-through and dir==1, output equals data_in>>1
    check_shift_right_vector: assert property (
        @(posedge A) (!passthrough && (dir == 1'b1)) |-> (data_out == right_shifted)
    );

    // Left shift zeros the LSB
    check_shift_left_lsb_zero: assert property (
        @(posedge A) (!passthrough && (dir == 1'b0)) |-> (data_out[0] == 1'b0)
    );

    // Left shift bit mapping: out[1] <= in[0]
    check_shift_left_bit1_map: assert property (
        @(posedge A) (!passthrough && (dir == 1'b0)) |-> (data_out[1] == data_in[0])
    );

    // Left shift bit mapping: out[2] <= in[1]
    check_shift_left_bit2_map: assert property (
        @(posedge A) (!passthrough && (dir == 1'b0)) |-> (data_out[2] == data_in[1])
    );

    // Left shift bit mapping: out[3] <= in[2]
    check_shift_left_bit3_map: assert property (
        @(posedge A) (!passthrough && (dir == 1'b0)) |-> (data_out[3] == data_in[2])
    );

    // Right shift zeros the MSB
    check_shift_right_msb_zero: assert property (
        @(posedge A) (!passthrough && (dir == 1'b1)) |-> (data_out[3] == 1'b0)
    );

    // Right shift bit mapping: out[2] <= in[3]
    check_shift_right_bit2_map: assert property (
        @(posedge A) (!passthrough && (dir == 1'b1)) |-> (data_out[2] == data_in[3])
    );

    // Right shift bit mapping: out[1] <= in[2]
    check_shift_right_bit1_map: assert property (
        @(posedge A) (!passthrough && (dir == 1'b1)) |-> (data_out[1] == data_in[2])
    );

    // Right shift bit mapping: out[0] <= in[1]
    check_shift_right_bit0_map: assert property (
        @(posedge A) (!passthrough && (dir == 1'b1)) |-> (data_out[0] == data_in[1])
    );

endmodule