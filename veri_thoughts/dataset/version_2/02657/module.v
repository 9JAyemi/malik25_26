module master_slave_ff ( input clk, input d, output reg q );
    always @(posedge clk)
        q <= d;
endmodule

module shift_register ( input clk, input d, output q );
    wire q1, q2, q3;
    master_slave_ff ff1(clk, d, q1);
    master_slave_ff ff2(clk, q1, q2);
    master_slave_ff ff3(clk, q2, q3);
    assign q = q3;
endmodule

module top_module ( input clk, input d, output q );
    shift_register sr(clk, d, q);
endmodule