
module taxicab_distance #(parameter N = 32)(
	input [N-1:0] x1, y1, x2, y2,
	output [N+1:0] dist
);

wire signed [N:0] dist_x12, dist_x21, dist_xabs, dist_y12, dist_y21, dist_yabs;

// Calculate the absolute difference between x1 and x2
assign dist_x12 = x1 - x2;
// Calculate the absolute difference between x2 and x1
assign dist_x21 = x2 - x1;

// Select the absolute difference between x1 and x2 if x1 > x2, otherwise select the absolute difference between x2 and x1
assign dist_xabs = (x1 > x2) ? dist_x12 : dist_x21;

// Calculate the absolute difference between y1 and y2
assign dist_y12 = y1 - y2;
// Calculate the absolute difference between y2 and y1
assign dist_y21 = y2 - y1;

// Select the absolute difference between y1 and y2 if y1 > y2, otherwise select the absolute difference between y2 and y1
assign dist_yabs = (y1 > y2) ? dist_y12 : dist_y21;

// Calculate the taxicab distance by adding the absolute differences of x and y coordinates
assign dist = dist_xabs + dist_yabs;

endmodule