// SVA for MAIN and register. Bind these to the DUT for checking and coverage.

package main_regfile_sva_pkg;

  // Assertions bound into MAIN
  module MAIN_sva #(parameter SIZE=5, parameter LEDSIZE=8) (
    input logic                 clk, Reset,
    input logic [SIZE-1:0]      Address,
    input logic                 RW, AB,
    input logic [1:0]           CS,
    input logic [LEDSIZE-1:0]   LED,
    input logic [31:0]          R_Data_A, R_Data_B,
    input logic [31:0]          LED_Data,
    input logic [31:0]          W_Data
  );

    default clocking cb @(posedge clk); endclocking
    default disable iff (Reset);

    localparam logic [31:0] C0 = 32'h1234_5678;
    localparam logic [31:0] C1 = 32'h89AB_CDEF;
    localparam logic [31:0] C2 = 32'h7FFF_FFFF;
    localparam logic [31:0] C3 = 32'hFFFF_FFFF;

    function automatic logic [31:0] cs2data(logic [1:0] cs);
      case (cs)
        2'b00: cs2data = C0;
        2'b01: cs2data = C1;
        2'b10: cs2data = C2;
        default: cs2data = C3;
      endcase
    endfunction

    // Structural/functional relationships
    assert property (LED_Data == (AB ? R_Data_A : R_Data_B));
    assert property (R_Data_A == R_Data_B); // same address on both ports

    // W_Data mapping and LED behavior
    assert property (RW  |-> (W_Data == cs2data(CS)));
    assert property (!RW |-> (W_Data == 32'h0));
    assert property (RW  |-> (LED == '0));

    // LED byte selection when reading
    assert property (!RW |->
        ((CS==2'b00 && LED==LED_Data[7:0])   ||
         (CS==2'b01 && LED==LED_Data[15:8])  ||
         (CS==2'b10 && LED==LED_Data[23:16]) ||
         (CS==2'b11 && LED==LED_Data[31:24])));

    // Write commits on next cycle (if checking same address)
    assert property (RW |-> ##1 (Address==$past(Address) |-> (R_Data_A == cs2data($past(CS)))));

    // Hold when no write and address stable
    assert property (!RW && $stable(Address) |-> ##1 (R_Data_A == $past(R_Data_A)));

    // Synchronous reset effects (do not disable)
    assert property (@(posedge clk) Reset |=> (R_Data_A==32'h0 && R_Data_B==32'h0 && LED=='0 && W_Data==32'h0));

    // Functional coverage
    cover property (@(posedge clk) Reset);
    cover property (RW && CS==2'b00);
    cover property (RW && CS==2'b01);
    cover property (RW && CS==2'b10);
    cover property (RW && CS==2'b11);
    cover property (!RW && CS==2'b00 && AB==0);
    cover property (!RW && CS==2'b01 && AB==1);
    cover property (!RW && CS==2'b10 && AB==0);
    cover property (!RW && CS==2'b11 && AB==1);
    cover property (RW ##1 (!RW && Address==$past(Address) && R_Data_A==cs2data($past(CS))));

  endmodule


  // Assertions bound into register
  module register_sva (
    input  logic        clk, Reset, Write_Reg,
    input  logic [4:0]  R_Addr_A, R_Addr_B, W_Addr,
    input  logic [31:0] W_Data,
    input  logic [31:0] R_Data_A, R_Data_B
  );

    default clocking cb @(posedge clk); endclocking
    default disable iff (Reset);

    // Read data matches storage
    assert property (R_Data_A == REGISTERS[R_Addr_A]);
    assert property (R_Data_B == REGISTERS[R_Addr_B]);

    // Write commits next cycle
    assert property (Write_Reg |=> (REGISTERS[$past(W_Addr)] == $past(W_Data)));

    // No-write holds targeted word
    assert property (!Write_Reg |=> (REGISTERS[$past(W_Addr)] == $past(REGISTERS[$past(W_Addr)])));

    // Reset clears all registers (checked per entry)
    genvar i;
    generate
      for (i=0; i<32; i++) begin : g_rst_clr
        assert property (@(posedge clk) Reset |=> (REGISTERS[i] == 32'h0));
      end
    endgenerate

    // Coverage
    cover property (Write_Reg);
    cover property (Reset);

  endmodule

endpackage


// Binds
import main_regfile_sva_pkg::*;

bind MAIN     MAIN_sva      #(.SIZE(SIZE), .LEDSIZE(LEDSIZE)) MAIN_sva_i (.*);
bind register register_sva                                   register_sva_i (.*);