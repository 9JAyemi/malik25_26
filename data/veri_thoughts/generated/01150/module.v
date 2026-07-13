module shift_register (
    input [3:0] DATA_IN,
    input LOAD,
    input CLK,
    output reg [3:0] DATA_OUT
);

    always @(posedge CLK) begin
        if (LOAD) begin
            DATA_OUT <= DATA_IN;
        end else begin
            DATA_OUT <= {DATA_OUT[2:0], DATA_OUT[3]};
        end
    end

endmodule