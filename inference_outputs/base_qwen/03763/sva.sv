```systemverilog
module fill_diode_sva (
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    output logic fill
);
    // Combinational logic: fill is determined by the inputs at the current clock edge
    comb_logic: assert property (
        @(posedge VPWR or posedge VGND or posedge VPB or posedge VNB) disable iff (!VPWR) (fill == ((VPWR & !VGND) | (!VPB & VNB)))
    );
endmodule
```