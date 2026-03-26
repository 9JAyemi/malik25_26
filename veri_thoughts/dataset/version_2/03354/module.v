module max_finder(
    input signed [7:0] A,
    input signed [7:0] B,
    input signed [7:0] C,
    output reg signed [7:0] max_val
);

always @ (*) begin
    max_val = (A > B) ? ((A > C) ? A : C) : ((B > C) ? B : C);
end

endmodule