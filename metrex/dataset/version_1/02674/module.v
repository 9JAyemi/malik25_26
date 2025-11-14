module switch_module
#(parameter     addr = 4'b0010)
(   
    input       [7:0] port0_i,
    input       [7:0] port1_i,
    input       [7:0] port0_local_i,
    input       [7:0] port1_local_i,
    output      [7:0] port0_o,
    output      [7:0] port1_o,
    output      portl0_ack,
    output      portl1_ack,
    input       clk,
    input       rst
);

    // inputs
    wire [7:0] port0_0, port1_0, port0_local_0, port1_local_0;

    assign port0_0 = (rst) ? 8'd0 : port0_i;
    assign port1_0 = (rst) ? 8'd0 : port1_i;
    assign port0_local_0 = (rst) ? 8'd0 : port0_local_i;
    assign port1_local_0 = (rst) ? 8'd0 : port1_local_i;

    	
	
    reg [7:0] port0_0_r, port1_0_r;
    always @(posedge clk) begin
        port0_0_r <= port0_0;
        port1_0_r <= port1_0;
    end

	wire ej_0 = port0_0_r[3:0] == addr && port0_0_r[4];
	wire ej_1 = port1_0_r[3:0] == addr && port1_0_r[4];

    assign port0_o = (ej_0) ? port0_0_r[7:0] : port0_local_0;
    assign port1_o = (ej_1) ? port1_0_r[7:0] : port1_local_0;

    wire valid0 = (ej_0) ? 0 : port0_0_r[4];
    wire valid1 = (ej_1) ? 0 : port1_0_r[4];

    assign portl0_ack = ~valid0 & (ej_0 | (port0_local_0[4] && ~ej_1));
    assign portl1_ack = ~valid1 & (ej_1 | (port1_local_0[4] && ~ej_0));

endmodule