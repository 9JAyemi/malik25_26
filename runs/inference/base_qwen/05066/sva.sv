module pcidec_new_sva (
    input logic clk_i,
    input logic nrst_i,
    input logic [31:0] ad_i,
    input logic [3:0] cbe_i,
    input logic idsel_i,
    input logic [31:25] bar0_i,
    input logic memEN_i,
    input logic pciadrLD_i,
    output logic adrcfg_o,
    output logic adrmem_o,
    output logic [24:1] adr_o,
    output logic [3:0] cmd_o
);
    reg [31:0] adr;
    reg [3:0] cmd;
    reg idsel_s;
    wire a1;

    always @(posedge clk_i or negedge nrst_i)
    begin
        if (!nrst_i)
        begin
            adr <= 23'b1111_1111_1111_1111_1111_111;
            cmd <= 3'b111;
            idsel_s <= 1'b0;
        end
        else if (pciadrLD_i)
        begin
            adr <= ad_i;
            cmd <= cbe_i;
            idsel_s <= idsel_i;
        end
    end

    assign adrmem_o = (
        (memEN_i == 1'b1) &&
        (adr[31:25] == bar0_i) &&
        (adr[1:0] == 2'b00) &&
        (cmd[3:1] == 3'b011)
    ) ? 1'b1 : 1'b0;

    assign adrcfg_o = (
        (idsel_s == 1'b1) &&
        (adr[1:0] == 2'b00) &&
        (cmd[3:1] == 3'b101)
    ) ? 1'b1 : 1'b0;

    assign a1 = ~ (cbe_i[3] && cbe_i[2]);
    assign adr_o = {adr[24:2], a1};
    assign cmd_o = cmd;

    // Reset behavior
    reset: assert property (
        @(posedge clk_i) disable iff (!nrst_i) (nrst_i == 1'b0)
    );

    // PCI address load behavior
    pciadrLD_check: assert property (
        @(posedge clk_i) disable iff (!nrst_i) (pciadrLD_i |-> (adr == ad_i) && (cmd == cbe_i) && (idsel_s == idsel_i))
    );

    // Address register behavior
    adr_reg_check: assert property (
        @(posedge clk_i) disable iff (!nrst_i) (pciadrLD_i |-> (adr == ad_i))
    );

    // Command register behavior
    cmd_reg_check: assert property (
        @(posedge clk_i) disable iff (!nrst_i) (pciadrLD_i |-> (cmd == cbe_i))
    );

    // ID select register behavior
    idsel_reg_check: assert property (
        @(posedge clk_i) disable iff (!nrst_i) (pciadrLD_i |-> (idsel_s == idsel_i))
    );

    // Memory enable behavior
    memEN_check: assert property (
        @(posedge clk_i) disable iff (!nrst_i) (memEN_i |-> (adrmem_o == ((adr[31:25] == bar0_i) && (adr[1:0] == 2'b00) && (cmd[3:1] == 3'b011))))
    );

    // Configuration enable behavior
    adrcfg_check: assert property (
        @(posedge clk_i) disable iff (!nrst_i) (idsel_s && (adr[1:0] == 2'b00) && (cmd[3:1] == 3'b101) |-> adrcfg_o == 1'b1)
    );

    // Address output behavior
    adr_o_check: assert property (
        @(posedge clk_i) disable iff (!nrst_i) (a1 |-> (adr_o == {adr[24:2], a1}))
    );

    // Command output behavior
    cmd_o_check: assert property (
        @(posedge clk_i) disable iff (!nrst_i) (cmd_o == cmd)
    );

    // a1 signal behavior
    a1_check: assert property (
        @(posedge clk_i) disable iff (!nrst_i) (a1 == ~ (cbe_i[3] && cbe_i[2]))
    );
endmodule