module power_management (
    output VIRTPWR,
    input SLEEP,
    input VPWR,
    input VPB,
    input VNB
);

    reg VIRTPWR_reg; // internal register to store VIRTPWR value

    always @(*) begin
        if (SLEEP == 1 || VPWR == 0 || VPB == 0 || VNB == 0) begin
            VIRTPWR_reg = 0;
        end else begin
            VIRTPWR_reg = 1;
        end
    end

    assign VIRTPWR = VIRTPWR_reg;

endmodule