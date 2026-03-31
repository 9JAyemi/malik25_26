
module binary_to_gray (
    input       [3:0]   in,
    input               load,
    output reg  [3:0]   out,
    output reg          valid
);

always @(posedge load) begin
    if (load) begin
        out     <= (in >> 1) ^ in;
        valid   <= 1;
    end
    else begin
        valid <= 0;
    end
end
endmodule