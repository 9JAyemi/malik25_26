module k580ww55_sva (
    input logic clk,
    input logic reset,
    input logic we_n,
    input logic [1:0] addr,
    input logic [7:0] idata,
    input logic [7:0] odata,
    input logic [7:0] opa,
    input logic [7:0] opb,
    input logic [7:0] opc
);

    // Reset drives all outputs to their defined reset values.
    check_reset_values: assert property (
        @(posedge clk) reset |-> (odata == 8'h00 && opa == 8'hFF && opb == 8'hFF && opc == 8'hFF)
    );

    // Address 00 makes odata reflect the previous opa value.
    check_odata_reads_opa: assert property (
        @(posedge clk) disable iff (reset) (addr == 2'b00) |=> (odata == $past(opa))
    );

    // Address 01 makes odata reflect the previous opb value.
    check_odata_reads_opb: assert property (
        @(posedge clk) disable iff (reset) (addr == 2'b01) |=> (odata == $past(opb))
    );

    // Address 10 makes odata reflect the previous opc value.
    check_odata_reads_opc: assert property (
        @(posedge clk) disable iff (reset) (addr == 2'b10) |=> (odata == $past(opc))
    );

    // Address 11 makes odata return zero.
    check_odata_zero_on_ctrl_addr: assert property (
        @(posedge clk) disable iff (reset) (addr == 2'b11) |=> (odata == 8'h00)
    );

    // A write to address 00 updates opa and leaves opb/opc unchanged.
    check_write_opa: assert property (
        @(posedge clk) disable iff (reset)
        (!we_n && (addr == 2'b00)) |=> (opa == $past(idata) && opb == $past(opb) && opc == $past(opc))
    );

    // A write to address 01 updates opb and leaves opa/opc unchanged.
    check_write_opb: assert property (
        @(posedge clk) disable iff (reset)
        (!we_n && (addr == 2'b01)) |=> (opa == $past(opa) && opb == $past(idata) && opc == $past(opc))
    );

    // A write to address 10 updates opc and leaves opa/opb unchanged.
    check_write_opc: assert property (
        @(posedge clk) disable iff (reset)
        (!we_n && (addr == 2'b10)) |=> (opa == $past(opa) && opb == $past(opb) && opc == $past(idata))
    );

    // A write to address 11 updates only the selected opc bit.
    check_write_opc_bit: assert property (
        @(posedge clk) disable iff (reset)
        (!we_n && (addr == 2'b11)) |=> (
            opa == $past(opa) &&
            opb == $past(opb) &&
            opc == (($past(opc) & ~(8'h01 << $past(idata[3:1]))) |
                    ({8{$past(idata[0])}} &  (8'h01 << $past(idata[3:1]))))
        )
    );

    // With write disabled, the output ports hold their previous values.
    check_no_write_holds_ports: assert property (
        @(posedge clk) disable iff (reset)
        we_n |=> (opa == $past(opa) && opb == $past(opb) && opc == $past(opc))
    );

endmodule