module dffrl (din, clk, rst_l, q, se, si, so);

parameter SIZE = 1;

input	[SIZE-1:0]	din ;	// data in
input			clk ;	// clk or scan clk
input			rst_l ;	// reset

output	[SIZE-1:0]	q ;	// output

input			se ;	// scan-enable
input	[SIZE-1:0]	si ;	// scan-input
output	[SIZE-1:0]	so ;	// scan-output

reg 	[SIZE-1:0]	q ;

always @ (posedge clk) begin
    if (rst_l == 1'b0) begin
        q <= {SIZE{1'b0}};
    end else begin
        q <= (se == 1'b1) ? si : din;
    end
end

assign so = q;

endmodule