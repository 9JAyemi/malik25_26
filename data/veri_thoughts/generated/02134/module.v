
module dffrl_async (din, clk, rst_l, q, se, si, so);

parameter SIZE = 1;

input   [SIZE-1:0]      din ;   // data in
input                   clk ;   // clk or scan clk
input                   rst_l ;   // reset

output  [SIZE-1:0]      q ;     // output

input                   se ;    // scan-enable
input   [SIZE-1:0]      si ;    // scan-input
output  [SIZE-1:0]      so ;    // scan-output

reg     [SIZE-1:0]      q ;

always @ (posedge clk or negedge rst_l) begin
	if (!rst_l)
		q[SIZE-1:0]  <= {SIZE{1'b0}};
	else begin
		if (se)
			q[SIZE-1:0]  <= si[SIZE-1:0];
		else
			q[SIZE-1:0]  <= din[SIZE-1:0];
	end
end

assign so[SIZE-1:0] = q[SIZE-1:0] ;

endmodule