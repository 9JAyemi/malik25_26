module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] shift,
    input logic dir,
    input logic [3:0] out
);
    // Combinational RTL with no reset/clock; assertions sample on 'clk'.

    // When dir==0, out equals right-path expression.
    check_dir0_function: assert property (
        @(posedge clk) (dir == 1'b0) |-> (out == ({in[1:0], 2'b00} >> shift))
    );

    // When dir==1, out equals left-path expression.
    check_dir1_function: assert property (
        @(posedge clk) (dir == 1'b1) |-> (out == ({2'b00, in[3:2]} << shift))
    );

    // dir==0, shift==0 maps low 2 bits to out[3:2], zeros in out[1:0].
    map_dir0_s0: assert property (
        @(posedge clk) (dir == 1'b0 && shift == 2'd0) |-> (out[3:2] == in[1:0] && out[1:0] == 2'b00)
    );

    // dir==0, shift==1 maps low 2 bits to out[2:1], zeros at out[3] and out[0].
    map_dir0_s1: assert property (
        @(posedge clk) (dir == 1'b0 && shift == 2'd1) |-> (out[3] == 1'b0 && out[2:1] == in[1:0] && out[0] == 1'b0)
    );

    // dir==0, shift==2 maps low 2 bits to out[1:0], zeros in out[3:2].
    map_dir0_s2: assert property (
        @(posedge clk) (dir == 1'b0 && shift == 2'd2) |-> (out[3:2] == 2'b00 && out[1:0] == in[1:0])
    );

    // dir==0, shift==3 maps in[1] to out[0], zeros in out[3:1].
    map_dir0_s3: assert property (
        @(posedge clk) (dir == 1'b0 && shift == 2'd3) |-> (out[3:1] == 3'b000 && out[0] == in[1])
    );

    // dir==1, shift==0 maps high 2 bits to out[1:0], zeros in out[3:2].
    map_dir1_s0: assert property (
        @(posedge clk) (dir == 1'b1 && shift == 2'd0) |-> (out[3:2] == 2'b00 && out[1:0] == in[3:2])
    );

    // dir==1, shift==1 maps high 2 bits to out[2:1], zeros at out[3] and out[0].
    map_dir1_s1: assert property (
        @(posedge clk) (dir == 1'b1 && shift == 2'd1) |-> (out[3] == 1'b0 && out[2:1] == in[3:2] && out[0] == 1'b0)
    );

    // dir==1, shift==2 maps high 2 bits to out[3:2], zeros in out[1:0].
    map_dir1_s2: assert property (
        @(posedge clk) (dir == 1'b1 && shift == 2'd2) |-> (out[3:2] == in[3:2] && out[1:0] == 2'b00)
    );

    // dir==1, shift==3 maps in[2] to out[3], zeros in out[2:0].
    map_dir1_s3: assert property (
        @(posedge clk) (dir == 1'b1 && shift == 2'd3) |-> (out[3] == in[2] && out[2:0] == 3'b000)
    );

endmodule