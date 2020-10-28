(* This software is governed by the CeCILL license under French law and
 * abiding by the rules of distribution of free software.  You can  use,
 * modify and/ or redistribute the software under the terms of the CeCILL
 * license as circulated by CEA, CNRS and INRIA at the following URL
 * "http://www.cecill.info".

 * As a counterpart to the access to the source code and  rights to copy,
 * modify and redistribute granted by the license, users are provided only
 * with a limited warranty  and the software's author,  the holder of the
 * economic rights,  and the successive licensors  have only  limited
 * liability.

 * In this respect, the user's attention is drawn to the risks associated
 * with loading,  using,  modifying and/or developing or reproducing the
 * software by the user in light of its specific status of free software,
 * that may mean  that it is complicated to manipulate,  and  that  also
 * therefore means  that it is reserved for developers  and  experienced
 * professionals having in-depth computer knowledge. Users are therefore
 * encouraged to load and test the software's suitability as regards their
 * requirements in conditions enabling the security of their systems and/or
 * data to be ensured and,  more generally, to use and operate it in the
 * same conditions as regards security.

 * The fact that you are presently reading this means that you have had
 * knowledge of the CeCILL license and that you accept its terms.
 *)

From Scheduler.SchedulerMockup Require Import CBool.
From Scheduler.SchedulerMockup Require Import CNat.
From Scheduler.SchedulerMockup Require Import Entry.
From Scheduler.SchedulerMockup Require Import JobSet.
From Scheduler.SchedulerMockup Require Import Jobs.
From Scheduler.SchedulerMockup Require Import State.
From Scheduler.SchedulerMockup Require Import CRet.

From Scheduler.PartitionMockup Require Import PipTypes.
From Scheduler.PartitionMockup Require Import PipWrappers.
From Scheduler.PartitionMockup Require Import Primitives.

From Scheduler.EDF Require Import EDF.

Require Extraction.
Extraction Language JSON.

Extraction Library CBool.
Extraction Library CNat.
Extraction Library Entry.
Extraction Library JobSet.
Extraction Library Jobs.
Extraction Library State.
Extraction Library CRet.
Extraction Library PipTypes.
Extraction Library PipWrappers.
Extraction Library Primitives.
Extraction Library EDF.
