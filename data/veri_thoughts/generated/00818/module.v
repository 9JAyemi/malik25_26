module dff (
    input DATAIN,
    input CLK,
    input ACLR,
    input ENA,
    input SCLR,
    input SLOAD,
    input SDATA,
    output reg Q
);

always @(posedge CLK, negedge ACLR) begin
    if (!ACLR) // Asynchronous clear
        Q <= 1'b0;
    else if (ENA) begin // Clock-enable
        if (SCLR) // Synchronous clear
            Q <= 1'b0;
        else if (SLOAD) // Synchronous load
            Q <= SDATA;
        else // Store DATAIN
            Q <= DATAIN;
    end
end

endmodule