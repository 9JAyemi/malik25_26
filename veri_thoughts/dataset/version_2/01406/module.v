module shift_register ( input clk, input d, output [2:0] q );
    wire d_in;
    wire [2:0] q_in;
    my_dff dff_inst ( .clk(clk), .d(d_in), .q(q_in[0]) );
    my_dff dff_inst1 ( .clk(clk), .d(q_in[0]), .q(q_in[1]) );
    my_dff dff_inst2 ( .clk(clk), .d(q_in[1]), .q(q_in[2]) );
    
    assign d_in = d;
    assign q = q_in;
endmodule

module my_dff ( input clk, input d, output q );
    reg q;
    always @(posedge clk) begin
        q <= d;
    end
endmodule