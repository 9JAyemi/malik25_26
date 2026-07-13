
module minimum_value (
    input [7:0] a, b, c, d,
    output [7:0] min_val_out
);

// Logic to find the minimum value among a, b, c, and d
assign min_val_out = (a < b) ? ((a < c) ? ((a < d) ? a : d) : ((c < d) ? c : d)) : ((b < c) ? ((b < d) ? b : d) : ((c < d) ? c : d));

endmodule
