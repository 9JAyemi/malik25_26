module omsp_wakeup_cell (

// OUTPUTs
    wkup_out,                  // Wakup signal (asynchronous)

// INPUTs
    scan_clk,                  // Scan clock
    scan_mode,                 // Scan mode
    scan_rst,                  // Scan reset
    wkup_clear,                // Glitch free wakeup event clear
    wkup_event                 // Glitch free asynchronous wakeup event
);

output wkup_out; // Wakup signal (asynchronous)

input scan_clk; // Scan clock
input scan_mode; // Scan mode
input scan_rst; // Scan reset
input wkup_clear; // Glitch free wakeup event clear
input wkup_event; // Glitch free asynchronous wakeup event


// Scan stuff for the ASIC mode
`ifdef ASIC
   wire wkup_rst;
   omsp_scan_mux scan_mux_rst (
                               .scan_mode    (scan_mode),
                               .data_in_scan (scan_rst),
                               .data_in_func (wkup_clear),
                               .data_out     (wkup_rst)
   );

   wire wkup_clk;
   omsp_scan_mux scan_mux_clk (
                               .scan_mode    (scan_mode),
                               .data_in_scan (scan_clk),
                               .data_in_func (wkup_event),
                               .data_out     (wkup_clk)
   );

`else
   wire wkup_rst  =  wkup_clear;
   wire wkup_clk  =  wkup_event;
`endif

// Wakeup capture
reg wkup_out;
always @(posedge wkup_clk or posedge wkup_rst)
  if (wkup_rst) wkup_out <= 1'b0;
  else wkup_out <= 1'b1;

endmodule