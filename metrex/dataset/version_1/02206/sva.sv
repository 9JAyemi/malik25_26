// SVA checker for ram_16x1k_sp
module ram_16x1k_sp_sva
(
  input logic        clka,
  input logic        ena,
  input logic [1:0]  wea,
  input logic [9:0]  addra,
  input logic [15:0] dina,
  input logic [15:0] douta
);
  default clocking cb @(posedge clka); endclocking

  localparam int DEPTH = 1024;

  // Reference model (write-first), validity tracks if address has been written
  logic [15:0] ref_mem [0:DEPTH-1];
  bit          ref_val [0:DEPTH-1];

  initial begin
    foreach (ref_mem[i]) ref_mem[i] = '0;
    foreach (ref_val[i]) ref_val[i] = 1'b0;
  end

  always_ff @(posedge clka) begin
    if (ena) begin
      unique case (wea)
        2'b01: begin ref_mem[addra][7:0]  <= dina[7:0];  ref_val[addra] <= 1'b1; end
        2'b10: begin ref_mem[addra][15:8] <= dina[15:8]; ref_val[addra] <= 1'b1; end
        2'b11: begin ref_mem[addra]       <= dina;       ref_val[addra] <= 1'b1; end
        default: /* no write */;
      endcase
    end
  end

  // Controls must be known when used
  assert property ( !$isunknown({ena,wea,addra}) );
  assert property ( ena && (wea==2'b01) |-> !$isunknown(dina[7:0]) );
  assert property ( ena && (wea==2'b10) |-> !$isunknown(dina[15:8]) );
  assert property ( ena && (wea==2'b11) |-> !$isunknown(dina) );

  // Read data matches reference model (post-NBA, write-first)
  assert property ( ##0 (ref_val[addra] -> (douta == ref_mem[addra])) );

  // Once written, output must be known
  assert property ( ref_val[addra] |-> !$isunknown(douta) );

  // No spurious change when address is stable and no write occurs
  assert property ( ($stable(addra) && (!ena || (wea==2'b00)) && ref_val[addra]) |-> $stable(douta) );

  // Byte-masking behavior on stable address
  assert property ( ($stable(addra) && ref_val[addra] && ena && (wea==2'b01)) |-> ##0 (douta[7:0]==dina[7:0]   && $stable(douta[15:8])) );
  assert property ( ($stable(addra) && ref_val[addra] && ena && (wea==2'b10)) |-> ##0 (douta[15:8]==dina[15:8] && $stable(douta[7:0])) );
  assert property ( ($stable(addra) && ena && (wea==2'b11))                   |-> ##0 (douta==dina) );

  // Functional coverage
  cover property ( ena && wea==2'b00 );
  cover property ( ena && wea==2'b01 );
  cover property ( ena && wea==2'b10 );
  cover property ( ena && wea==2'b11 );
  cover property ( ena && wea!=2'b00 ##1 ena && wea!=2'b00 ); // back-to-back writes
  cover property ( ena && wea==2'b01 ##1 ena && wea==2'b10 && $past(addra)==addra ); // both bytes to same addr
  cover property ( ena && wea==2'b11 && addra==10'h000 ); // low address
  cover property ( ena && wea!=2'b00 && addra==10'h3FF ); // high address
endmodule

bind ram_16x1k_sp ram_16x1k_sp_sva i_ram_16x1k_sp_sva (.*);