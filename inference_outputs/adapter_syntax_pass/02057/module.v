module shift_register (
    input in,
    input shift,
    output reg out
);

    reg [7:0] register;

    always @(posedge shift) begin
        register <= {in, register[7:1]};
    end

    always @* begin
        out = register[7];
    end

endmodule