// SVA for mod_pmc
// Concise, quality-focused checks and coverage

module mod_pmc_sva #(
  parameter ADDR_INT            = 32'h0000_0000,
  parameter ADDR_MISS_I         = 32'h0000_0004,
  parameter ADDR_MISS_D         = 32'h0000_0008,
  parameter ADDR_ACC_I          = 32'h0000_000c,
  parameter ADDR_ACC_D          = 32'h0000_0010,
  parameter ADDR_UART_RECV      = 32'h0000_0014,
  parameter ADDR_UART_SEND      = 32'h0000_0018
)(
  input        clk,
  input        rst,
  input [31:0] daddr,
  input [31:0] iout,
  input [31:0] dout,
  // event inputs
  input pmc_int, pmc_cache_miss_I, pmc_cache_miss_D,
        pmc_cache_access_I, pmc_cache_access_D,
        pmc_uart_recv, pmc_uart_send,
  // internal counters
  input [31:0] count_int,
  input [31:0] count_cache_miss_I,
  input [31:0] count_cache_miss_D,
  input [31:0] count_cache_access_I,
  input [31:0] count_cache_access_D,
  input [31:0] count_uart_recv,
  input [31:0] count_uart_send
);

  // default sampling at negedge (design updates on negedge)
  default clocking cb @(negedge clk); endclocking

  // Basic interface sanity (single-bit events, iout constant)
  assert property (pmc_int inside {1'b0,1'b1}
                && pmc_cache_miss_I inside {1'b0,1'b1}
                && pmc_cache_miss_D inside {1'b0,1'b1}
                && pmc_cache_access_I inside {1'b0,1'b1}
                && pmc_cache_access_D inside {1'b0,1'b1}
                && pmc_uart_recv inside {1'b0,1'b1}
                && pmc_uart_send inside {1'b0,1'b1});
  assert property (iout == 32'h0);

  // Reset clears all counters on the next negedge
  assert property (rst |=> (count_int==0
                         && count_cache_miss_I==0
                         && count_cache_miss_D==0
                         && count_cache_access_I==0
                         && count_cache_access_D==0
                         && count_uart_recv==0
                         && count_uart_send==0));

  // Next-state updates (when not in reset): count_next = count + event
  assert property (!rst |=> count_int             == $past(count_int)             + $past(pmc_int));
  assert property (!rst |=> count_cache_miss_I    == $past(count_cache_miss_I)    + $past(pmc_cache_miss_I));
  assert property (!rst |=> count_cache_miss_D    == $past(count_cache_miss_D)    + $past(pmc_cache_miss_D));
  assert property (!rst |=> count_cache_access_I  == $past(count_cache_access_I)  + $past(pmc_cache_access_I));
  assert property (!rst |=> count_cache_access_D  == $past(count_cache_access_D)  + $past(pmc_cache_access_D));
  assert property (!rst |=> count_uart_recv       == $past(count_uart_recv)       + $past(pmc_uart_recv));
  assert property (!rst |=> count_uart_send       == $past(count_uart_send)       + $past(pmc_uart_send));

  // No counter changes on posedge (only updates on negedge)
  assert property (@(posedge clk)
                   $stable({count_int,
                            count_cache_miss_I, count_cache_miss_D,
                            count_cache_access_I, count_cache_access_D,
                            count_uart_recv, count_uart_send}));

  // Combinational read mux correctness for dout
  assert property (
    dout == (daddr==ADDR_INT       ? count_int :
             daddr==ADDR_MISS_I    ? count_cache_miss_I :
             daddr==ADDR_MISS_D    ? count_cache_miss_D :
             daddr==ADDR_ACC_I     ? count_cache_access_I :
             daddr==ADDR_ACC_D     ? count_cache_access_D :
             daddr==ADDR_UART_RECV ? count_uart_recv :
             daddr==ADDR_UART_SEND ? count_uart_send :
             32'h0)
  );

  // Functional coverage
  // Reset/release observed
  cover property (rst ##1 !rst);

  // Each counter increments at least once
  cover property (!rst && pmc_int            ##1 count_int            == $past(count_int)+1);
  cover property (!rst && pmc_cache_miss_I   ##1 count_cache_miss_I   == $past(count_cache_miss_I)+1);
  cover property (!rst && pmc_cache_miss_D   ##1 count_cache_miss_D   == $past(count_cache_miss_D)+1);
  cover property (!rst && pmc_cache_access_I ##1 count_cache_access_I == $past(count_cache_access_I)+1);
  cover property (!rst && pmc_cache_access_D ##1 count_cache_access_D == $past(count_cache_access_D)+1);
  cover property (!rst && pmc_uart_recv      ##1 count_uart_recv      == $past(count_uart_recv)+1);
  cover property (!rst && pmc_uart_send      ##1 count_uart_send      == $past(count_uart_send)+1);

  // Each mapped address accessed at least once
  cover property (daddr==ADDR_INT);
  cover property (daddr==ADDR_MISS_I);
  cover property (daddr==ADDR_MISS_D);
  cover property (daddr==ADDR_ACC_I);
  cover property (daddr==ADDR_ACC_D);
  cover property (daddr==ADDR_UART_RECV);
  cover property (daddr==ADDR_UART_SEND);

  // Wrap-around coverage (optional but useful)
  cover property (!rst && count_int==32'hFFFF_FFFF && pmc_int            |=> count_int==32'h0000_0000);
  cover property (!rst && count_cache_miss_I==32'hFFFF_FFFF && pmc_cache_miss_I |=> count_cache_miss_I==32'h0000_0000);
  cover property (!rst && count_cache_miss_D==32'hFFFF_FFFF && pmc_cache_miss_D |=> count_cache_miss_D==32'h0000_0000);
  cover property (!rst && count_cache_access_I==32'hFFFF_FFFF && pmc_cache_access_I |=> count_cache_access_I==32'h0000_0000);
  cover property (!rst && count_cache_access_D==32'hFFFF_FFFF && pmc_cache_access_D |=> count_cache_access_D==32'h0000_0000);
  cover property (!rst && count_uart_recv==32'hFFFF_FFFF && pmc_uart_recv |=> count_uart_recv==32'h0000_0000);
  cover property (!rst && count_uart_send==32'hFFFF_FFFF && pmc_uart_send |=> count_uart_send==32'h0000_0000);

endmodule

// Bind into the DUT to access internal counters
bind mod_pmc mod_pmc_sva #(
  .ADDR_INT(32'h0000_0000),
  .ADDR_MISS_I(32'h0000_0004),
  .ADDR_MISS_D(32'h0000_0008),
  .ADDR_ACC_I(32'h0000_000c),
  .ADDR_ACC_D(32'h0000_0010),
  .ADDR_UART_RECV(32'h0000_0014),
  .ADDR_UART_SEND(32'h0000_0018)
) mod_pmc_sva_i (
  .clk(clk),
  .rst(rst),
  .daddr(daddr),
  .iout(iout),
  .dout(dout),
  .pmc_int(pmc_int),
  .pmc_cache_miss_I(pmc_cache_miss_I),
  .pmc_cache_miss_D(pmc_cache_miss_D),
  .pmc_cache_access_I(pmc_cache_access_I),
  .pmc_cache_access_D(pmc_cache_access_D),
  .pmc_uart_recv(pmc_uart_recv),
  .pmc_uart_send(pmc_uart_send),
  .count_int(count_int),
  .count_cache_miss_I(count_cache_miss_I),
  .count_cache_miss_D(count_cache_miss_D),
  .count_cache_access_I(count_cache_access_I),
  .count_cache_access_D(count_cache_access_D),
  .count_uart_recv(count_uart_recv),
  .count_uart_send(count_uart_send)
);