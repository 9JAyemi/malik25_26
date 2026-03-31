module binary_multiplier_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [7:0] out
);
    // Combinational DUT with no clock/reset; sample on any input edge.

    // out equals the sum of b shifted by each a bit position.
    check_out_matches_shift_sum: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3] or
          posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3])
        out == (b + (b << a[0]) + (b << a[1]) + (b << a[2]) + (b << a[3]))
    );

    // When a[0]==0, out equals b.
    check_a0_zero_identity: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3] or
          posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3])
        (a[0] == 1'b0) |-> (out == b)
    );

    // When a[1]==0, out equals b.
    check_a1_zero_identity: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3] or
          posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3])
        (a[1] == 1'b0) |-> (out == b)
    );

    // When a[2]==0, out equals b.
    check_a2_zero_identity: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3] or
          posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3])
        (a[2] == 1'b0) |-> (out == b)
    );

    // When a[3]==0, out equals b.
    check_a3_zero_identity: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3] or
          posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3])
        (a[3] == 1'b0) |-> (out == b)
    );

    // When all a bits are 0, out equals b.
    check_all_a_zero_identity: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3] or
          posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3])
        (a == 4'b0000) |-> (out == b)
    );

    // When all a bits are 1, out equals 8*b.
    check_all_a_one_doubling: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3] or
          posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3])
        (a == 4'b1111) |-> (out == (b << 3))
    );

    // When a==0 and b==0, out is 0.
    check_zero_inputs_zero_out: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3] or
          posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3])
        (a == 4'b0000 && b == 4'b0000) |-> (out == 8'h00)
    );

    // When a==1 and b==1, out is 1.
    check_one_inputs_one_out: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3] or
          posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3])
        (a == 4'b0001 && b == 4'b0001) |-> (out == 8'h01)
    );

    // When a==15 and b==1, out is 128.
    check_max_inputs_max_out: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3] or
          posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3])
        (a == 4'b1111 && b == 4'b0001) |-> (out == 8'h80)
    );

    // When a==15 and b==15, out is 255.
    check_max_inputs_max_out_255: assert property (
        @(posedge a[0] or negedge a[0] or
          posedge a[1] or negedge a[1] or
          posedge a[2] or negedge a[2] or
          posedge a[3] or negedge a[3] or
          posedge b[0] or negedge b[0] or
          posedge b[1] or negedge b[1] or
          posedge b[2] or negedge b[2] or
          posedge b[3] or negedge b[3])
        (a == 4'b1111 && b == 4'b1111) |-> (out == 8'hFF)
    );

endmodule