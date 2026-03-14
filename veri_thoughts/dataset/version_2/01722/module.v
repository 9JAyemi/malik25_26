module ExtToIntSync(
    input clk,
    input rst,
    input ext_signal,
    output reg int_signal
);

always @ (posedge clk or posedge rst) begin
    if (rst) begin
        int_signal <= 0;
    end else begin
        int_signal <= ext_signal;
    end
end

endmodule

