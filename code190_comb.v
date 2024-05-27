/**************************************************************************/
/* code190_comb.v                          For CSC.T341 CLD Archlab TOKYO TECH */
/**************************************************************************/
`timescale 1ns/100ps
`default_nettype none //

/***** top module for simulation *****/
module m_top (); 
  reg r_clk=0; initial forever #50 r_clk = ~r_clk;
  wire [31:0] w_led;

//  initial $dumpfile("main.vcd");
//  initial $dumpvars(0, m_top);

  reg [31:0] r_cnt = 1;
  always@(posedge r_clk) r_cnt <= r_cnt + 1;
   
  m_proc14 p (r_clk, 1'b1, w_led);

  always@(posedge r_clk) $write("%7d %08x\n", r_cnt, p.Wb_rslt2);
//  initial begin5
//     $write("clock: r_pc     IfId_pc  IdEx_pc  ExMe_pc  MeWb_pc : ");
//     $write("t Id_rrs1  Id_rrs2  Ex_ain   Ex_rslt  Wb_rslt2 w_led\n");
//  end
//  always@(posedge r_clk) 
//    $write("%5d: %08x %08x %08x %08x %08x: %d %08x %08x %08x %08x %08x %08x\n", 
//           r_cnt, p.r_pc, p.IfId_pc, p.IdEx_pc, p.ExMe_pc, p.MeWb_pc,  
//           p.Ex_taken, p.Id_rrs1, p.Id_rrs2, p.Ex_ain, p.Ex_rslt, p.Wb_rslt2, p.w_led);
  always@(posedge r_clk) if(w_led!=0) $finish;
  initial #50000000 $finish;
endmodule

/***** main module for FPGA implementation *****/
/*
module m_main (w_clk, w_led);
  input  wire w_clk;
  output wire [3:0] w_led;
 
  wire w_clk2, w_locked;
  clk_wiz_0 clk_w0 (w_clk2, 0, w_locked, w_clk);
   
  wire [31:0] w_dout;
  m_proc14 p (w_clk2, w_locked, w_dout);

  vio_0 vio_00(w_clk2, w_dout);
 
  reg [3:0] r_led = 0;
  always @(posedge w_clk2) 
    r_led <= {^w_dout[31:24], ^w_dout[23:16], ^w_dout[15:8], ^w_dout[7:0]};
  assign w_led = r_led;
endmodule
*/

/**************************************************************************/
module m_proc14 (w_clk, w_ce, w_led);
  input  wire w_clk, w_ce;
  output wire [31:0] w_led;

  reg [31:0] r_pc      = 0; // program counter
  reg [31:0] IfId_pc   = 0; // IfId pipeline registers
  reg [31:0] IfId_ir   = 0;

  reg [31:0] IdEx_pc   = 0; // IdEx pipeline registers
  reg [31:0] IdEx_ir   = 0;   
  reg [31:0] IdEx_tpc  = 0;
  reg [31:0] IdEx_rrs1 = 0;
  reg [31:0] IdEx_rrs2 = 0;   
  reg [31:0] IdEx_imm  = 0;
  reg [4:0]  IdEx_rd   = 0;

  reg [31:0] ExMe_pc   = 0; // ExMe pipeline registers
  reg [31:0] ExMe_ir   = 0;
  reg [31:0] ExMe_rslt = 0;
  reg [31:0] ExMe_rrs2 = 0;
  reg [4:0]  ExMe_rd   = 0;

  reg [31:0] MeWb_pc   = 0; // MeWb pipeline registers
  reg [31:0] MeWb_ir   = 0;
  reg [31:0] MeWb_rslt = 0;
  reg [31:0] MeWb_ldd  = 0;
  reg [4:0]  MeWb_rd   = 0;
  /*********************** IF stage *********************************/
  wire [31:0] If_ir;
  m_amemory m_imem (w_clk, r_pc[13:2], 1'd0, 32'd0, If_ir);
  always @(posedge w_clk) #5 if(w_ce) begin
    IfId_pc <= (Ex_taken || w_vb_comb) ? 0 : r_pc;
    IfId_ir <= (Ex_taken || w_vb_comb) ? {25'd0, 7'b0010011} : If_ir;
  end
  /*********************** ID stage *********************************/
  wire [4:0] Id_op5 = IfId_ir[6:2];
  wire [4:0] Id_rs1 = IfId_ir[19:15];
  wire [4:0] Id_rs2 = IfId_ir[24:20];
  wire [4:0] Id_rd  = IfId_ir[11:7];
  wire Id_we = (Id_op5==5'b01100 || Id_op5==5'b00100 || Id_op5==5'b00000);
  wire [31:0] Id_imm, Id_rrs1, Id_rrs2;
  m_immgen m_immgen0 (IfId_ir, Id_imm);
  m_rf_bypass m_regs (w_clk, Id_rs1, Id_rs2, MeWb_rd, 1'b1, Wb_rslt2, Id_rrs1, Id_rrs2);
  always @(posedge w_clk) #5 if(w_ce) begin
    IdEx_pc   <= (Ex_taken || w_vb_comb) ? 0 : IfId_pc;
    IdEx_ir   <= (Ex_taken || w_vb_comb) ? {25'd0, 7'b0010011} : IfId_ir;
    IdEx_tpc  <= IfId_pc + Id_imm;
    IdEx_imm  <= Id_imm;
    IdEx_rrs1 <= Id_rrs1;
    IdEx_rrs2 <= Id_rrs2;
    IdEx_rd   <= (Id_we==0 || Ex_taken || w_vb_comb) ? 0 : Id_rd; // Note
  end
  /*********************** Ex stage *********************************/
  // comb addi
  wire [0:0]  w_vb_comb;
  wire [31:0] w_imm_comb;
  wire [11:0] w_addr_comb;
  m_combiner_addi m_comb(w_clk, {IdEx_ir, IdEx_pc, IdEx_imm}, w_vb_comb, w_imm_comb, w_addr_comb);

  wire [4:0] Ex_op5 = IdEx_ir[6:2];
  wire [4:0] Ex_rs1 = IdEx_ir[19:15]; // 5/23
  wire [4:0] Ex_rs2 = IdEx_ir[24:20]; // 5/23
  wire Ex_SLL = (IdEx_ir[14:12]==3'b001);
  wire Ex_SRL = (IdEx_ir[14:12]==3'b101);
  wire Ex_BEQ = ({IdEx_ir[12], Ex_op5}==6'b011000);
  wire Ex_BNE = ({IdEx_ir[12], Ex_op5}==6'b111000);
  wire [31:0] Ex_ain1 = (Ex_rs1==0) ? 0 : (Ex_rs1==Me_rd & Me_we) ? ExMe_rslt : (Ex_rs1==Wb_rd & Wb_we) ? Wb_rslt2 : IdEx_rrs1; // 5/23
  wire [31:0] Ex_ain2 = (Ex_rs2==0) ? 0 : (Ex_rs2==Me_rd & Me_we) ? ExMe_rslt : (Ex_rs2==Wb_rd & Wb_we) ? Wb_rslt2 : IdEx_rrs2; // 5/23
  wire [31:0] Ex_ain = (Ex_op5==5'b01100 || Ex_op5==5'b11000) ? Ex_ain2 : (w_vb_comb) ? w_imm_comb : IdEx_imm; // 5/23
  wire [31:0] Ex_rslt = (Ex_SLL) ? Ex_ain1 << Ex_ain[4:0] : // 5/23
                        (Ex_SRL) ? Ex_ain1 >> Ex_ain[4:0] : Ex_ain1 + Ex_ain; // 5/23
  wire Ex_taken = (Ex_BEQ & Ex_ain1==Ex_ain) || (Ex_BNE & Ex_ain1!=Ex_ain); // 5/23
  always @(posedge w_clk) #5 if(w_ce) begin
    ExMe_pc   <= IdEx_pc;
    ExMe_ir   <= IdEx_ir;
    ExMe_rslt <= Ex_rslt;
    ExMe_rrs2 <= IdEx_rrs2;
    ExMe_rd   <= IdEx_rd;
  end
  /*********************** Me stage *********************************/
  wire [4:0] Me_op5 = ExMe_ir[6:2];   
  wire [4:0] Me_rd = ExMe_rd; // 5/23
  wire       Me_we = (Me_op5==5'b01100 || Me_op5==5'b00100 || Me_op5==5'b00000);
  wire [31:0] Me_ldd;
  m_amemory m_dmem (w_clk, ExMe_rslt[13:2], (Me_op5==5'b01000), ExMe_rrs2, Me_ldd);
  always @(posedge w_clk) #5 if(w_ce) begin
     MeWb_pc   <= ExMe_pc;
     MeWb_ir   <= ExMe_ir;
     MeWb_rslt <= ExMe_rslt;
     MeWb_ldd  <= Me_ldd;
     MeWb_rd   <= ExMe_rd;
  end
  /*********************** Wb stage *********************************/
  wire Wb_LW = (MeWb_ir[6:2]==5'b00000);
  wire [4:0] Wb_op5 = MeWb_ir[6:2]; // 5/23
  wire [4:0] Wb_rd = MeWb_rd; // 5/23
  wire       Wb_we = (Wb_op5==5'b01100 || Wb_op5==5'b00100 || Wb_op5==5'b00000); // 5/23
  wire [31:0] Wb_rslt2 = (Wb_LW) ? MeWb_ldd : MeWb_rslt;
  always @(posedge w_clk) #5
    if(w_ce && IfId_ir!=32'h000f0033) r_pc <= (Ex_taken) ? IdEx_tpc : (w_vb_comb) ? {18'b0, w_addr_comb, 2'b00}+4: r_pc+4;
   
  reg [31:0] r_led = 0;
  always @(posedge w_clk) if(w_ce & MeWb_rd==30) r_led <= Wb_rslt2;
  assign w_led = r_led;
endmodule

/**************************************************************************/
module m_amemory (w_clk, w_addr, w_we, w_din, w_dout); // asynchronous memory
  input  wire w_clk, w_we;
  input  wire [11:0] w_addr;
  input  wire [31:0] w_din;
  output wire [31:0] w_dout;
  reg [31:0] 	     cm_ram [0:4095]; // 4K word (4096 x 32bit) memory
  always @(posedge w_clk) if (w_we) cm_ram[w_addr] <= w_din;
  assign #20 w_dout = cm_ram[w_addr];
`include "program.txt"
endmodule

/**************************************************************************/
module m_memory (w_clk, w_addr, w_we, w_din, r_dout); // synchronous memory
  input  wire w_clk, w_we;
  input  wire [11:0] w_addr;
  input  wire [31:0] w_din;
  output reg  [31:0] r_dout;
  reg [31:0]         cm_ram [0:4095]; // 4K word (4096 x 32bit) memory
  always @(posedge w_clk) if (w_we) cm_ram[w_addr] <= w_din;
  always @(posedge w_clk) r_dout <= cm_ram[w_addr];
`include "program.txt"
endmodule

/**************************************************************************/
module m_immgen (w_i, r_imm); // module immediate generator
  input  wire [31:0] w_i;    // instruction
  output reg  [31:0] r_imm;  // r_immediate

  always @(*) case (w_i[6:2])
    5'b11000: r_imm <= {{20{w_i[31]}}, w_i[7], w_i[30:25], w_i[11:8], 1'b0};   // B-type
    5'b01000: r_imm <= {{21{w_i[31]}}, w_i[30:25], w_i[11:7]};                 // S-type
    5'b11011: r_imm <= {{12{w_i[31]}}, w_i[19:12], w_i[20], w_i[30:21], 1'b0}; // J-type
    5'b01101: r_imm <= {w_i[31:12], 12'b0};                                    // U-type
    5'b00101: r_imm <= {w_i[31:12], 12'b0};                                    // U-type
    default : r_imm <= {{21{w_i[31]}}, w_i[30:20]};                   // I-type & R-type
  endcase
endmodule

/**************************************************************************/
module m_rf_bypass (w_clk, w_rr1, w_rr2, w_wr, w_we, w_wdata, w_rdata1, w_rdata2); // 5/23
   input  wire        w_clk;
   input  wire [4:0]  w_rr1, w_rr2, w_wr;
   input  wire [31:0] w_wdata;
   input  wire        w_we;
   output wire [31:0] w_rdata1, w_rdata2;
    
   reg [31:0] r[0:31];
   assign #8 w_rdata1 = (w_rr1==0) ? 0 : (w_rr1==w_wr & w_we) ? w_wdata : r[w_rr1]; // 5/23
   assign #8 w_rdata2 = (w_rr2==0) ? 0 : (w_rr2==w_wr & w_we) ? w_wdata : r[w_rr2]; // 5/23
   always @(posedge w_clk) if(w_we) r[w_wr] <= w_wdata;
endmodule

/**************************************************************************/
module m_combiner_addi (w_clk, w_all, w_vb, w_dout, w_addr_out); 
  input  wire w_clk;
  input  wire [95:0] w_all;
  output wire [0:0] w_vb;
  output wire [31:0] w_dout;
  output wire [11:0] w_addr_out;
  wire [31:0] w_ir  = w_all[95:64];
  wire [31:0] w_pc  = w_all[63:32];
  wire [31:0] w_imm = w_all[31:0];
  reg [31:0] r_srt = 0;
  reg [49:0] 	     cm_ram [0:4095]; 
  wire [11:0] w_addr = w_pc[13:2];
  integer i;

  initial begin 
    for (i = 0; i < 4095; i = i + 1) begin
        cm_ram[i] = 0;  
    end
  end

  assign #8 w_vb = (w_ir[6:2]==5'b00100 && w_ir[19:15]==w_ir[11:7] && cm_ram[w_addr][49:49]) ? (cm_ram[w_addr][43:32] - w_addr > 2) : 0;
  assign #8 w_dout = (w_ir[6:2]==5'b00100 && w_ir[19:15]==w_ir[11:7] && cm_ram[w_addr][49:49]) ? cm_ram[w_addr][31:0] : 0;
  assign #8 w_addr_out = (w_ir[6:2]==5'b00100 && w_ir[19:15]==w_ir[11:7] && cm_ram[w_addr][49:49]) ? cm_ram[w_addr][43:32] : 0;

  always @(posedge w_clk) #5 if (w_ir[6:2]==5'b00100 && w_ir[19:15]==w_ir[11:7] && ~cm_ram[w_addr][49:49]) begin 
    cm_ram[w_addr][48:44] <= w_all[75:71];
    cm_ram[w_addr][31:0] <= w_all[31:0];
    if (w_addr!=0 && cm_ram[w_addr-1][48:44]==w_ir[11:7]) begin 
    cm_ram[cm_ram[w_addr-1][43:32]][43:32] <= w_all[45:34];
    cm_ram[cm_ram[w_addr-1][43:32]][31:0] <= cm_ram[cm_ram[w_addr-1][43:32]][31:0] + w_all[31:0];
    cm_ram[w_addr][49:49] <= 1'b0;
    cm_ram[w_addr][43:32] <= cm_ram[w_addr-1][43:32];
    end else begin 
    cm_ram[w_addr][49:49] <= 1'b1;
    cm_ram[w_addr][43:32] <= w_all[45:34];
    end
  end

`include "program.txt"
endmodule
/**************************************************************************/